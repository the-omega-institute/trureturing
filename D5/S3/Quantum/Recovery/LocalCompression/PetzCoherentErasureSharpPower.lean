/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A coherent three-flag dephasing witness for the sharp half power. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The coherent and block-diagonal square roots give two
different ordinary Petz outputs for the same retained likelihood. Their
protected flag probabilities and paired defect are evaluated as functions
of the witness parameter.
-/

import D5.S3.Quantum.CommutingMidpoint.Fidelity
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import D5.S3.Weil.ZetaLinear.RankTrace

/-! The coherent three-flag example in `coherent-erasure-sharp-half-witness.txt`.
The retained qubit is the first coordinate. Flags 0, 1, 2 correspond to
labels 1, 2, 3 of the witness. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzCoherentErasureSharpPower

open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMFlagRefinement
  (lift lift_eq_joint marginal marginal_eq_sum partialTracePetz)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt)
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)

set_option autoImplicit false

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
abbrev JointIndex := Fin 2 × Fin 3
abbrev Joint := Matrix JointIndex JointIndex ℂ

section RankOne

variable {n : Type*}

/-- The rank-one matrix of a ket, which is an orthogonal projection for a unit ket. -/
def projector (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

private theorem projector_psd [Finite n] (v : n → ℂ) : (projector v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

variable [Fintype n]

private theorem projector_trace (v : n → ℂ) : (projector v).trace = star v ⬝ᵥ v := by
  rw [projector, Matrix.trace_vecMulVec, dotProduct_comm]

private theorem projector_sq (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    projector v * projector v = projector v := by
  simp [projector, Matrix.vecMulVec_mul_vecMulVec, hv]

private theorem projector_sandwich (v : n → ℂ) (A : Matrix n n ℂ) :
    projector v * A * projector v = (star v ⬝ᵥ (A *ᵥ v)) • projector v := by
  rw [Matrix.mul_assoc]
  unfold projector
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

private theorem trace_mul_projector (A : Matrix n n ℂ) (v : n → ℂ) :
    (A * projector v).trace = star v ⬝ᵥ (A *ᵥ v) := by
  rw [projector, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

private theorem conjugate_projector (S : Matrix n n ℂ) (v : n → ℂ) :
    S * projector v * Sᴴ = projector (S *ᵥ v) := by
  unfold projector
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

omit [Fintype n] in
private theorem projector_real_smul (c : ℝ) (v : n → ℂ) :
    projector (c • v) = (c * c) • projector v := by
  simp only [projector, star_smul, star_trivial, Matrix.smul_vecMulVec,
    Matrix.vecMulVec_smul, smul_smul]

end RankOne

/-- The qubit block at a specified flag. -/
def block (X : Joint) (f : Fin 3) : Qubit :=
  X.submatrix (fun i => (i, f)) (fun j => (j, f))

/-- Embed a qubit operator at one flag. -/
def atFlag (f : Fin 3) (A : Qubit) : Joint :=
  Matrix.blockDiagonal (fun g => if g = f then A else 0)

private theorem atFlag_mul (f : Fin 3) (A B : Qubit) :
    atFlag f A * atFlag f B = atFlag f (A * B) := by
  unfold atFlag
  rw [← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext g
  change (if g = f then A else 0) * (if g = f then B else 0) =
    if g = f then A * B else 0
  by_cases h : g = f <;> simp [h]

/-- The projective effect of reading the indicated environment label. -/
def flagProj (f : Fin 3) : Joint :=
  Matrix.diagonal (fun i => if i.2 = f then 1 else 0)

private theorem flagProj_eq (f : Fin 3) : flagProj f = atFlag f 1 := by
  ext ⟨i, g⟩ ⟨j, h⟩
  by_cases hgh : g = h
  · subst h
    by_cases hgf : g = f <;> by_cases hij : i = j <;>
      simp [flagProj, atFlag, Prod.mk.injEq, hij, hgf]
  · simp [flagProj, atFlag, Matrix.blockDiagonal_apply, Prod.mk.injEq, hgh]

private theorem flagProj_sq (f : Fin 3) : flagProj f * flagProj f = flagProj f := by
  rw [flagProj_eq, atFlag_mul, Matrix.one_mul]

private theorem flagProj_psd (f : Fin 3) : (flagProj f).PosSemidef := by
  unfold flagProj
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases h : i.2 = f <;> simp [h]

theorem flagProj_complete : (∑ f : Fin 3, flagProj f) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [flagProj, Matrix.sum_apply, Finset.sum_ite_eq]
  · simp [flagProj, Matrix.sum_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem dephase_kraus_normalized : (∑ f : Fin 3, (flagProj f)ᴴ * flagProj f) = 1 := by
  calc
    _ = ∑ f : Fin 3, flagProj f := by
      apply Finset.sum_congr rfl
      intro f _
      rw [(flagProj_psd f).isHermitian.eq, flagProj_sq]
    _ = 1 := flagProj_complete

/-- Projective dephasing of the environment, with the qubit left intact. -/
def dephase (X : Joint) : Joint := ∑ f : Fin 3, flagProj f * X * flagProj f

theorem dephase_is_channel :
    ∃ channel : QuantumChannel JointIndex JointIndex, ∀ X : Joint,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = dephase X := by
  obtain ⟨channel, h⟩ := finite_kraus_quantum_channel flagProj dephase_kraus_normalized
  refine ⟨channel, fun X => ?_⟩
  simpa only [dephase, (flagProj_psd _).isHermitian.eq] using h X

theorem dephase_eq_blocks (X : Joint) : dephase X = Matrix.blockDiagonal (block X) := by
  ext ⟨i, g⟩ ⟨j, h⟩
  by_cases he : g = h
  · subst h
    simp [dephase, flagProj, Matrix.sum_apply, Matrix.blockDiagonal_apply_eq, block,
      Matrix.submatrix_apply, Finset.sum_ite_eq]
  · simp [dephase, flagProj, Matrix.sum_apply, Matrix.blockDiagonal_apply, he]

private theorem block_add (X Y : Joint) (f : Fin 3) : block (X + Y) f = block X f + block Y f :=
  rfl

private theorem block_smul (c : ℝ) (X : Joint) (f : Fin 3) :
    block (c • X) f = c • block X f := rfl

private theorem block_atFlag (f g : Fin 3) (A : Qubit) :
    block (atFlag f A) g = if g = f then A else 0 := by
  ext i j
  simp [block, atFlag, Matrix.blockDiagonal_apply_eq]

theorem marginal_dephase (X : Joint) : partialTraceRight (dephase X) = partialTraceRight X := by
  rw [dephase_eq_blocks]
  change marginal (block X) = _
  rw [marginal_eq_sum]
  ext i j
  simp [block, partialTraceRight, Matrix.sum_apply]

/-- The protected flag probability is the Born pairing with the projective flag effect. -/
def protectedProbability (X : Joint) (f : Fin 3) : ℝ := (flagProj f * X).trace.re

theorem protectedProbability_blockDiagonal (B : Fin 3 → Qubit) (f : Fin 3) :
    protectedProbability (Matrix.blockDiagonal B) f = (B f).trace.re := by
  rw [protectedProbability, flagProj_eq, atFlag, ← Matrix.blockDiagonal_mul,
    Matrix.trace_blockDiagonal]
  change (∑ g : Fin 3, ((if g = f then (1 : Qubit) else 0) * B g).trace).re = _
  have ht (g : Fin 3) :
      ((if g = f then (1 : Qubit) else 0) * B g).trace =
        if g = f then (B f).trace else 0 := by
    by_cases h : g = f
    · subst g
      simp
    · simp [h]
  simp only [ht, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

def e : Fin 2 → ℂ := ![1, 0]
def psi1 : Fin 2 → ℂ := ![0, 1]
def psi2 (eps : ℝ) : Fin 2 → ℂ :=
  ![(Real.sqrt eps : ℂ), (Real.sqrt (1 - eps : ℝ) : ℂ)]

private def flagKets (eps : ℝ) : Fin 3 → Fin 2 → ℂ := ![psi1, psi2 eps, 0]

/-- The coherent superposition over the first two flags. -/
def chi (eps : ℝ) : JointIndex → ℂ :=
  fun i => (Real.sqrt (1 / 2 : ℝ) : ℂ) * flagKets eps i.2 i.1

private theorem complex_sqrt_sq {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
  exact_mod_cast Real.sq_sqrt hx

private theorem e_unit : star e ⬝ᵥ e = 1 := by
  norm_num [e, dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def]

private theorem psi1_unit : star psi1 ⬝ᵥ psi1 = 1 := by
  norm_num [psi1, dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def]

private theorem psi2_unit (eps : ℝ) (he : 0 ≤ eps) (he' : eps ≤ 1) :
    star (psi2 eps) ⬝ᵥ psi2 eps = 1 := by
  calc
    _ = (Real.sqrt eps : ℂ)^2 + (Real.sqrt (1 - eps : ℝ) : ℂ)^2 := by
      simp [psi2, dotProduct, Fin.sum_univ_two, Pi.star_apply, pow_two]
    _ = 1 := by
      rw [complex_sqrt_sq he, complex_sqrt_sq (sub_nonneg.mpr he')]
      push_cast
      ring

private theorem chi_unit (eps : ℝ) (he : 0 ≤ eps) (he' : eps ≤ 1) :
    star (chi eps) ⬝ᵥ chi eps = 1 := by
  have hhalf : (Real.sqrt (1 / 2 : ℝ) : ℂ)^2 = 1 / 2 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      complex_sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ = (Real.sqrt (1 / 2 : ℝ) : ℂ)^2 *
        (star psi1 ⬝ᵥ psi1 + star (psi2 eps) ⬝ᵥ psi2 eps) := by
      simp [chi, flagKets, dotProduct, Fintype.sum_prod_type_right, Fin.sum_univ_three,
        Fin.sum_univ_two, Pi.star_apply]
      ring
    _ = 1 := by rw [hhalf, psi1_unit, psi2_unit eps he he']; norm_num

private theorem block_projector_chi (eps : ℝ) (f : Fin 3) :
    block (projector (chi eps)) f = (1 / 2 : ℝ) • projector (flagKets eps f) := by
  have h :
      (fun i : Fin 2 => chi eps (i, f)) = Real.sqrt (1 / 2 : ℝ) • flagKets eps f := by
    ext i
    simp [chi, Pi.smul_apply, Complex.real_smul]
  change projector (fun i : Fin 2 => chi eps (i, f)) = _
  rw [h, projector_real_smul, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private theorem flagProj_mul_chi (eps : ℝ) :
    flagProj 2 * projector (chi eps) = 0 := by
  ext ⟨i, f⟩ j
  fin_cases f <;>
    simp [flagProj, chi, flagKets, projector, Matrix.vecMulVec_apply]

private theorem chi_mul_flagProj (eps : ℝ) :
    projector (chi eps) * flagProj 2 = 0 := by
  ext i ⟨j, f⟩
  fin_cases f <;>
    simp [flagProj, chi, flagKets, projector, Matrix.vecMulVec_apply, Pi.star_apply]

/-- The physical joint reference, including the coherent cross-flag entries. -/
def sigma (eps : ℝ) : Joint :=
  (1 / 2 : ℝ) • projector (chi eps) + (1 / 4 : ℝ) • flagProj 2

def lambda (eps : ℝ) : ℝ := 4 / (1 + eps)
def p (eps : ℝ) : ℝ := eps / (1 + eps)

/-- The candidate retained likelihood, whose physical identification is below. -/
def M (eps : ℝ) : Qubit := lambda eps • projector e

private theorem lambda_nonneg (eps : ℝ) (he : 0 < eps) : 0 ≤ lambda eps := by
  unfold lambda
  positivity

private theorem lambda_mul_eps (eps : ℝ) : lambda eps * eps = 4 * p eps := by
  unfold lambda p
  ring

private theorem lambda_quarter (eps : ℝ) (he : 0 < eps) : lambda eps / 4 = 1 - p eps := by
  have hd : 1 + eps ≠ 0 := by positivity
  unfold lambda p
  field_simp [hd]
  ring

theorem sigma_posSemidef (eps : ℝ) : (sigma eps).PosSemidef :=
  ((projector_psd _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
    ((flagProj_psd _).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))

/-- The diagonal flag blocks of the input reference. -/
def referenceBlocks (eps : ℝ) : Fin 3 → Qubit :=
  ![(1 / 4 : ℝ) • projector psi1, (1 / 4 : ℝ) • projector (psi2 eps),
    (1 / 4 : ℝ) • (1 : Qubit)]

theorem sigma_blocks (eps : ℝ) : block (sigma eps) = referenceBlocks eps := by
  funext f
  rw [sigma, block_add, block_smul, block_smul, block_projector_chi, flagProj_eq,
    block_atFlag, smul_smul]
  fin_cases f <;> norm_num [flagKets, referenceBlocks, projector, Matrix.vecMulVec_zero]

theorem dephase_sigma (eps : ℝ) :
    dephase (sigma eps) = Matrix.blockDiagonal (referenceBlocks eps) := by
  rw [dephase_eq_blocks, sigma_blocks]

/-- The actual retained reference. -/
def Q (eps : ℝ) : Qubit := partialTraceRight (sigma eps)

theorem Q_eq (eps : ℝ) :
    Q eps = (1 / 4 : ℝ) • projector psi1 + (1 / 4 : ℝ) • projector (psi2 eps) +
      (1 / 4 : ℝ) • (1 : Qubit) := by
  rw [Q, ← marginal_dephase, dephase_sigma]
  change marginal (referenceBlocks eps) = _
  rw [marginal_eq_sum]
  simp [referenceBlocks, Fin.sum_univ_three]

theorem Q_posDef (eps : ℝ) : (Q eps).PosDef := by
  rw [Q_eq]
  exact Matrix.PosDef.posSemidef_add
    (((projector_psd psi1).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)).add
      ((projector_psd (psi2 eps)).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)))
    (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 4))

theorem Q_floor (eps : ℝ) : (1 / 4 : ℝ) • (1 : Qubit) ≤ Q eps := by
  rw [Q_eq, add_comm]
  exact le_add_of_nonneg_right
    (((projector_psd psi1).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)).add
      ((projector_psd (psi2 eps)).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))).nonneg

theorem sigma_trace (eps : ℝ) (he : 0 < eps) (he' : eps < 1) : (sigma eps).trace = 1 := by
  rw [← trace_partialTraceRight, ← Q, Q_eq]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, projector_trace,
    psi1_unit, psi2_unit eps he.le he'.le, Fintype.card_fin]
  norm_num [Complex.real_smul]

private theorem M_diagonal (eps : ℝ) :
    M eps = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (lambda eps : ℂ) else 0) := by
  ext i j
  rw [M, Matrix.smul_apply, projector, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [e, Complex.real_smul]

private theorem lift_M_diagonal (eps : ℝ) :
    lift (ι := Fin 3) (M eps) =
      Matrix.diagonal (fun i : JointIndex => if i.1 = 0 then (lambda eps : ℂ) else 0) := by
  rw [lift_eq_joint, M_diagonal]
  ext ⟨i, f⟩ ⟨j, g⟩
  by_cases hq : i = j <;> by_cases hf : f = g <;>
    simp [Matrix.blockDiagonal_apply, Prod.mk.injEq, hq, hf]

private theorem expectation_M_psi1 (eps : ℝ) :
    star psi1 ⬝ᵥ (M eps *ᵥ psi1) = 0 := by
  simp [M_diagonal, psi1, dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]

private theorem expectation_M_psi2 (eps : ℝ) (he : 0 ≤ eps) :
    star (psi2 eps) ⬝ᵥ (M eps *ᵥ psi2 eps) = ((lambda eps * eps : ℝ) : ℂ) := by
  calc
    _ = (lambda eps : ℂ) * (Real.sqrt eps : ℂ)^2 := by
      simp [M_diagonal, psi2, dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
      ring
    _ = _ := by rw [complex_sqrt_sq he, Complex.ofReal_mul]

private theorem expectation_lift_M_chi (eps : ℝ) (he : 0 ≤ eps) :
    star (chi eps) ⬝ᵥ (lift (ι := Fin 3) (M eps) *ᵥ chi eps) =
      ((2 * p eps : ℝ) : ℂ) := by
  have hhalf : (Real.sqrt (1 / 2 : ℝ) : ℂ)^2 = 1 / 2 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      complex_sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ = (lambda eps : ℂ) * (Real.sqrt eps : ℂ)^2 * (Real.sqrt (1 / 2 : ℝ) : ℂ)^2 := by
      simp [lift_M_diagonal, chi, flagKets, psi1, psi2, dotProduct, Fintype.sum_prod_type_right,
        Fin.sum_univ_three, Pi.star_apply, Matrix.mulVec_diagonal]
      ring
    _ = _ := by
      rw [complex_sqrt_sq he, hhalf, ← Complex.ofReal_mul, lambda_mul_eps]
      push_cast
      ring

private theorem Q_apply_zero (eps : ℝ) (he : 0 ≤ eps) :
    Q eps 0 0 = (((1 + eps) / 4 : ℝ) : ℂ) := by
  rw [Q_eq]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
    projector, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.one_apply_eq]
  simp [psi1, psi2, ← pow_two, complex_sqrt_sq he]
  ring

private theorem Q_expectation_e (eps : ℝ) (he : 0 ≤ eps) :
    star e ⬝ᵥ (Q eps *ᵥ e) = (((1 + eps) / 4 : ℝ) : ℂ) := by
  simpa [e, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply] using Q_apply_zero eps he

/-- The retained source and the true joint source on the third flag. -/
def P (eps : ℝ) : Qubit := CFC.sqrt (Q eps) * M eps * CFC.sqrt (Q eps)
def rho (eps : ℝ) : Joint := atFlag 2 (P eps)

theorem source_marginal (eps : ℝ) : partialTraceRight (rho eps) = P eps := by
  change marginal (fun g : Fin 3 => if g = 2 then P eps else 0) = _
  rw [marginal_eq_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem dephase_rho (eps : ℝ) : dephase (rho eps) = rho eps := by
  rw [dephase_eq_blocks]
  exact congrArg Matrix.blockDiagonal (funext fun f => block_atFlag 2 f (P eps))

def sourceKet (eps : ℝ) : JointIndex → ℂ :=
  fun i => if i.2 = 2 then
    (Real.sqrt (lambda eps) • (CFC.sqrt (Q eps) *ᵥ e)) i.1 else 0

theorem rho_eq_projector (eps : ℝ) (he : 0 < eps) : rho eps = projector (sourceKet eps) := by
  let S := CFC.sqrt (Q eps)
  let v : Fin 2 → ℂ := Real.sqrt (lambda eps) • (S *ᵥ e)
  have hs : Sᴴ = S := (CFC.sqrt_nonneg (Q eps)).posSemidef.isHermitian.eq
  have hp : P eps = projector v := by
    dsimp only [v]
    rw [projector_real_smul, ← pow_two, Real.sq_sqrt (lambda_nonneg eps he),
      ← conjugate_projector, hs]
    simp only [P, M, Matrix.mul_smul, Matrix.smul_mul, S]
  rw [rho, hp]
  ext ⟨i, f⟩ ⟨j, g⟩
  change (if f = g then (if f = 2 then projector v else 0) i j else 0) =
    (if f = 2 then v i else 0) * star (if g = 2 then v j else 0)
  by_cases hf : f = 2
  · subst f
    by_cases hg : g = 2
    · subst g
      simp only [eq_self, ite_true, projector, Matrix.vecMulVec_apply, Pi.star_apply]
    · simp [Ne.symm hg, hg]
  · by_cases hfg : f = g
    · subst g
      simp [hf]
    · simp [hf, hfg]

theorem rho_trace (eps : ℝ) (he : 0 < eps) : (rho eps).trace = 1 := by
  rw [← trace_partialTraceRight, source_marginal, P, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self _ (Q_posDef eps).posSemidef.nonneg]
  rw [M, Matrix.mul_smul, Matrix.trace_smul, trace_mul_projector, Q_expectation_e eps he.le]
  have hd : 1 + eps ≠ 0 := by positivity
  have hn : lambda eps * ((1 + eps) / 4) = 1 := by
    unfold lambda
    field_simp [hd]
  rw [Complex.real_smul, ← Complex.ofReal_mul, hn, Complex.ofReal_one]

theorem sourceKet_unit (eps : ℝ) (he : 0 < eps) :
    star (sourceKet eps) ⬝ᵥ sourceKet eps = 1 := by
  rw [← projector_trace, ← rho_eq_projector eps he, rho_trace eps he]

theorem rho_posSemidef (eps : ℝ) (he : 0 < eps) : (rho eps).PosSemidef := by
  rw [rho_eq_projector eps he]
  exact projector_psd _

/-- Kernel inclusion expressing that the physical source is supported by the joint reference. -/
theorem rho_supported (eps : ℝ) (v : JointIndex → ℂ)
    (hv : sigma eps *ᵥ v = 0) : rho eps *ᵥ v = 0 := by
  have hσ : flagProj 2 * sigma eps = (1 / 4 : ℝ) • flagProj 2 := by
    simp [sigma, Matrix.mul_add, flagProj_mul_chi, flagProj_sq]
  have hρ : rho eps * flagProj 2 = rho eps := by
    rw [rho, flagProj_eq, atFlag_mul, Matrix.mul_one]
  have h : ((1 / 4 : ℝ) • flagProj 2) *ᵥ v = 0 := by
    rw [← hσ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rw [Matrix.smul_mulVec] at h
  have hz : flagProj 2 *ᵥ v = 0 := (smul_eq_zero.mp h).resolve_left (by norm_num)
  calc
    rho eps *ᵥ v = (rho eps * flagProj 2) *ᵥ v := by rw [hρ]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]

/-- Positive square-root witness for the coherent reference. -/
def sigmaRoot (eps : ℝ) : Joint :=
  Real.sqrt (1 / 2 : ℝ) • projector (chi eps) + (1 / 2 : ℝ) • flagProj 2

theorem sqrt_sigma (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    CFC.sqrt (sigma eps) = sigmaRoot eps := by
  apply CFC.sqrt_unique
  · simp only [sigmaRoot, sigma, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, projector_sq _ (chi_unit eps he.le he'.le),
      chi_mul_flagProj, flagProj_mul_chi, flagProj_sq, smul_zero, add_zero, zero_add]
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  · exact (((projector_psd _).smul (Real.sqrt_nonneg _)).add
      ((flagProj_psd _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2))).nonneg

private theorem blockDiagonal_psd (B : Fin 3 → Qubit) (hB : ∀ f, (B f).PosSemidef) :
    (Matrix.blockDiagonal B).PosSemidef := by
  let S : Fin 3 → Qubit := fun f => CFC.sqrt (B f)
  have hs : (fun f => (S f)ᴴ) = S := by
    funext f
    exact (CFC.sqrt_nonneg (B f)).posSemidef.isHermitian.eq
  have hsq : (fun f => S f * S f) = B := by
    funext f
    exact CFC.sqrt_mul_sqrt_self _ (hB f).nonneg
  have hh := Matrix.posSemidef_conjTranspose_mul_self (Matrix.blockDiagonal S)
  rwa [Matrix.blockDiagonal_conjTranspose, hs, ← Matrix.blockDiagonal_mul, hsq] at hh

/-- Positive root blocks of the physically dephased reference. -/
def dephasedRootBlocks (eps : ℝ) : Fin 3 → Qubit :=
  ![(1 / 2 : ℝ) • projector psi1, (1 / 2 : ℝ) • projector (psi2 eps),
    (1 / 2 : ℝ) • (1 : Qubit)]

private theorem dephasedRootBlocks_psd (eps : ℝ) (f : Fin 3) :
    (dephasedRootBlocks eps f).PosSemidef := by
  fin_cases f
  · exact (projector_psd _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · exact (projector_psd _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · exact Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem sqrt_dephase_sigma (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    CFC.sqrt (dephase (sigma eps)) = Matrix.blockDiagonal (dephasedRootBlocks eps) := by
  rw [dephase_sigma]
  apply CFC.sqrt_unique _ (blockDiagonal_psd _ (dephasedRootBlocks_psd eps)).nonneg
  rw [← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext f
  change dephasedRootBlocks eps f * dephasedRootBlocks eps f = referenceBlocks eps f
  fin_cases f <;>
    norm_num [dephasedRootBlocks, referenceBlocks, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, projector_sq _ psi1_unit, projector_sq _ (psi2_unit eps he.le he'.le)]

private theorem dephase_sigma_psd (eps : ℝ) : (dephase (sigma eps)).PosSemidef := by
  rw [dephase_sigma]
  apply blockDiagonal_psd
  intro f
  fin_cases f
  · exact (projector_psd _).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
  · exact (projector_psd _).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
  · exact Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)

section InverseRoot

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem mpow_half_eq_sqrt {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    mpow A (1 / 2) = CFC.sqrt A := by
  rw [mpow, CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hA.nonneg]

private theorem mpow_neg_half_eq_inverseRoot {A : Matrix n n ℂ} (hA : A.PosDef) :
    mpow A (-(1 / 2)) = spectralInverseSqrt A := by
  unfold mpow spectralInverseSqrt
  apply cfc_congr
  intro x hx
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  change hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) =
    (Real.sqrt (hA.isHermitian.eigenvalues i))⁻¹
  rw [Real.rpow_neg (hA.eigenvalues_pos i).le, Real.sqrt_eq_rpow]

private theorem inverseRoot_cancel {A : Matrix n n ℂ} (hA : A.PosDef) :
    spectralInverseSqrt A * CFC.sqrt A = 1 ∧ CFC.sqrt A * spectralInverseSqrt A = 1 := by
  rw [CFC.sqrt_eq_real_sqrt _ hA.posSemidef.nonneg, cfcₙ_eq_cfc, spectralInverseSqrt,
    ← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _),
    ← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  have h (x : ℝ) (hx : x ∈ spectrum ℝ A) : Real.sqrt x ≠ 0 := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ne_of_gt (Real.sqrt_pos.mpr (hA.eigenvalues_pos i))
  have hc : cfc (fun _ : ℝ => (1 : ℝ)) A = 1 :=
    cfc_const_one ℝ A (ha := hA.isHermitian.isSelfAdjoint)
  constructor
  · rw [← hc]
    exact cfc_congr fun x hx => inv_mul_cancel₀ (h x hx)
  · rw [← hc]
    exact cfc_congr fun x hx => mul_inv_cancel₀ (h x hx)

end InverseRoot

theorem marginal_likelihood (eps : ℝ) :
    spectralInverseSqrt (partialTraceRight (sigma eps)) *
        partialTraceRight (rho eps) *
        spectralInverseSqrt (partialTraceRight (sigma eps)) = M eps := by
  rw [← Q, source_marginal, P]
  obtain ⟨hleft, hright⟩ := inverseRoot_cancel (Q_posDef eps)
  let S := CFC.sqrt (Q eps)
  let W := spectralInverseSqrt (Q eps)
  change W * (S * M eps * S) * W = M eps
  calc
    _ = (W * S) * M eps * (S * W) := by noncomm_ring
    _ = M eps := by rw [show W * S = 1 from hleft, show S * W = 1 from hright, one_mul, mul_one]

private theorem petz_eq_sandwich (eps : ℝ) (T : Joint) (hT : T.PosSemidef)
    (hm : partialTraceRight T = Q eps) :
    partialTracePetz T (partialTraceRight (rho eps)) =
      CFC.sqrt T * lift (ι := Fin 3) (M eps) * CFC.sqrt T := by
  unfold partialTracePetz
  rw [mpow_half_eq_sqrt hT, hm, mpow_neg_half_eq_inverseRoot (Q_posDef eps)]
  have h := marginal_likelihood eps
  change spectralInverseSqrt (Q eps) * partialTraceRight (rho eps) *
    spectralInverseSqrt (Q eps) = M eps at h
  dsimp only
  rw [h]

/-- Transport the ordinary Petz benchmark through the projective dephasing. -/
def Y0 (eps : ℝ) : Joint :=
  dephase (partialTracePetz (sigma eps) (partialTraceRight (rho eps)))

/-- Recompute the ordinary Petz benchmark from the dephased source and reference. -/
def Y1 (eps : ℝ) : Joint :=
  partialTracePetz (dephase (sigma eps)) (partialTraceRight (dephase (rho eps)))

private theorem flagProj_mul_lift (A : Qubit) :
    flagProj 2 * lift (ι := Fin 3) A = atFlag 2 A := by
  rw [flagProj_eq, lift_eq_joint]
  unfold atFlag
  rw [← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext f
  change (if f = 2 then (1 : Qubit) else 0) * A = if f = 2 then A else 0
  by_cases h : f = 2 <;> simp [h]

private theorem lift_mul_flagProj (A : Qubit) :
    lift (ι := Fin 3) A * flagProj 2 = atFlag 2 A := by
  rw [flagProj_eq, lift_eq_joint]
  unfold atFlag
  rw [← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext f
  change A * (if f = 2 then (1 : Qubit) else 0) = if f = 2 then A else 0
  by_cases h : f = 2 <;> simp [h]

private theorem atFlag_mul_flagProj (A : Qubit) : atFlag 2 A * flagProj 2 = atFlag 2 A := by
  rw [flagProj_eq, atFlag_mul, Matrix.mul_one]

private theorem smul_sandwich {n : Type*} [Fintype n] (A B C : Matrix n n ℂ) (a c : ℝ) :
    (a • A) * B * (c • C) = (a * c) • (A * B * C) := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem root_sandwich (eps : ℝ) (he : 0 < eps) :
    sigmaRoot eps * lift (ι := Fin 3) (M eps) * sigmaRoot eps =
      p eps • projector (chi eps) + (1 / 4 : ℝ) • atFlag 2 (M eps) := by
  let L := lift (ι := Fin 3) (M eps)
  let C := projector (chi eps)
  let F := flagProj 2
  have hCF : C * L * F = 0 := by
    rw [Matrix.mul_assoc, show L * F = F * L from
      (lift_mul_flagProj _).trans (flagProj_mul_lift _).symm,
      ← Matrix.mul_assoc, show C * F = 0 from chi_mul_flagProj eps, Matrix.zero_mul]
  have hFC : F * L * C = 0 := by
    rw [show F * L = L * F from
      (flagProj_mul_lift _).trans (lift_mul_flagProj _).symm,
      Matrix.mul_assoc, show F * C = 0 from flagProj_mul_chi eps, Matrix.mul_zero]
  have hCC : C * L * C = (2 * p eps) • C := by
    change projector (chi eps) * lift (ι := Fin 3) (M eps) * projector (chi eps) = _
    rw [projector_sandwich, expectation_lift_M_chi eps he.le]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (2 * p eps) C).symm
  have hFF : F * L * F = atFlag 2 (M eps) := by
    exact (congrArg (· * flagProj 2) (flagProj_mul_lift (M eps))).trans (atFlag_mul_flagProj _)
  let a := Real.sqrt (1 / 2 : ℝ)
  let b : ℝ := 1 / 2
  change (a • C + b • F) * L * (a • C + b • F) = _
  have hc : (a * a) * (2 * p eps) = p eps := by
    rw [← pow_two, show a ^ 2 = (1 / 2 : ℝ) from Real.sq_sqrt (by norm_num)]
    ring
  have hb : b * b = 1 / 4 := by norm_num [b]
  calc
    _ = ((a • C) * L * (a • C) + (a • C) * L * (b • F)) +
        ((b • F) * L * (a • C) + (b • F) * L * (b • F)) := by
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    _ = _ := by
      simp only [smul_sandwich, hCC, hCF, hFC, hFF, smul_zero, zero_add, add_zero, smul_smul,
        hc, hb, C]

theorem Y0_eq (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    Y0 eps = Matrix.blockDiagonal
      ![(p eps / 2) • projector psi1, (p eps / 2) • projector (psi2 eps),
        (1 / 4 : ℝ) • M eps] := by
  rw [Y0, petz_eq_sandwich eps _ (sigma_posSemidef eps) rfl, sqrt_sigma eps he he',
    root_sandwich eps he, dephase_eq_blocks]
  apply congrArg Matrix.blockDiagonal
  funext f
  rw [block_add, block_smul, block_smul, block_projector_chi, block_atFlag, smul_smul]
  fin_cases f <;> simp [flagKets, projector, div_eq_mul_inv]

theorem Y1_eq (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    Y1 eps = Matrix.blockDiagonal
      ![0, p eps • projector (psi2 eps), (1 / 4 : ℝ) • M eps] := by
  rw [Y1, dephase_rho, petz_eq_sandwich eps _ (dephase_sigma_psd eps) (marginal_dephase _),
    sqrt_dephase_sigma eps he he', lift_eq_joint, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext f
  change dephasedRootBlocks eps f * M eps * dephasedRootBlocks eps f = _
  fin_cases f
  · change ((1 / 2 : ℝ) • projector psi1) * M eps *
        ((1 / 2 : ℝ) • projector psi1) = 0
    rw [smul_sandwich, projector_sandwich, expectation_M_psi1, zero_smul, smul_zero]
  · change ((1 / 2 : ℝ) • projector (psi2 eps)) * M eps *
        ((1 / 2 : ℝ) • projector (psi2 eps)) = p eps • projector (psi2 eps)
    have hc : ((1 / 2 : ℝ) * (1 / 2)) * (lambda eps * eps) = p eps := by
      rw [lambda_mul_eps]
      ring
    have hsmul : ((lambda eps * eps : ℝ) : ℂ) • projector (psi2 eps) =
        (lambda eps * eps) • projector (psi2 eps) :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
    rw [smul_sandwich, projector_sandwich, expectation_M_psi2 eps he.le, hsmul, smul_smul, hc]
  · norm_num [dephasedRootBlocks, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem protected_Y0 (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    protectedProbability (Y0 eps) = ![p eps / 2, p eps / 2, 1 - p eps] := by
  funext f
  rw [Y0_eq eps he he', protectedProbability_blockDiagonal]
  fin_cases f
  · change ((p eps / 2) • projector psi1).trace.re = p eps / 2
    rw [Matrix.trace_smul, projector_trace, psi1_unit, Complex.real_smul, mul_one,
      Complex.ofReal_re]
  · change ((p eps / 2) • projector (psi2 eps)).trace.re = p eps / 2
    rw [Matrix.trace_smul, projector_trace, psi2_unit eps he.le he'.le, Complex.real_smul,
      mul_one, Complex.ofReal_re]
  · change ((1 / 4 : ℝ) • M eps).trace.re = 1 - p eps
    rw [M, smul_smul, Matrix.trace_smul, projector_trace, e_unit, Complex.real_smul,
      mul_one, Complex.ofReal_re, ← lambda_quarter eps he]
    ring

theorem protected_Y1 (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    protectedProbability (Y1 eps) = ![0, p eps, 1 - p eps] := by
  funext f
  rw [Y1_eq eps he he', protectedProbability_blockDiagonal]
  fin_cases f
  · change (0 : Qubit).trace.re = 0
    rw [Matrix.trace_zero, Complex.zero_re]
  · change (p eps • projector (psi2 eps)).trace.re = p eps
    rw [Matrix.trace_smul, projector_trace, psi2_unit eps he.le he'.le, Complex.real_smul,
      mul_one, Complex.ofReal_re]
  · change ((1 / 4 : ℝ) • M eps).trace.re = 1 - p eps
    rw [M, smul_smul, Matrix.trace_smul, projector_trace, e_unit, Complex.real_smul,
      mul_one, Complex.ofReal_re, ← lambda_quarter eps he]
    ring

/-- The half-density defect paired with the actual retained likelihood. -/
def Gamma (eps : ℝ) : ℝ :=
  (lift (ι := Fin 3) (M eps) * (Y1 eps - Y0 eps)).trace.re

theorem Gamma_eq (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    Gamma eps = 2 * (p eps)^2 := by
  have h1 : (M eps * projector psi1).trace = 0 := by
    rw [trace_mul_projector, expectation_M_psi1]
  have h2 : (M eps * projector (psi2 eps)).trace = ((lambda eps * eps : ℝ) : ℂ) := by
    rw [trace_mul_projector, expectation_M_psi2 eps he.le]
  rw [Gamma, Y0_eq eps he he', Y1_eq eps he he', lift_eq_joint,
    ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal]
  simp [Fin.sum_univ_three, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul,
    h1, h2, Complex.real_smul, Complex.mul_re, lambda_mul_eps]
  ring

open D5.S3.Quantum.CommutingMidpoint (rootFidelity)

private theorem p_pos (eps : ℝ) (he : 0 < eps) : 0 < p eps := by
  unfold p
  exact div_pos he (by linarith)

private theorem shared_block_eq (eps : ℝ) (he : 0 < eps) :
    (1 / 4 : ℝ) • M eps = (1 - p eps) • projector e := by
  rw [M, smul_smul, show (1 / 4 : ℝ) * lambda eps = lambda eps / 4 by ring,
    lambda_quarter eps he]

private theorem trace_smul_projector {v : Fin 2 → ℂ} (a : ℝ)
    (hv : star v ⬝ᵥ v = 1) : (a • projector v).trace = (a : ℂ) := by
  rw [Matrix.trace_smul, projector_trace, hv, Complex.real_smul, mul_one]

/-- Both ordinary Petz outputs are density matrices, including the zero block of Y1. -/
theorem Y0_Y1_density (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    ((Y0 eps).PosSemidef ∧ (Y0 eps).trace = 1) ∧
      ((Y1 eps).PosSemidef ∧ (Y1 eps).trace = 1) := by
  have hp := (p_pos eps he).le
  have hq : 0 ≤ 1 - p eps := by
    rw [← lambda_quarter eps he]
    exact div_nonneg (lambda_nonneg eps he) (by norm_num)
  have hd (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : a + b + (1 - p eps) = 1) :
      (Matrix.blockDiagonal
        ![a • projector psi1, b • projector (psi2 eps), (1 - p eps) • projector e]).PosSemidef ∧
      (Matrix.blockDiagonal
        ![a • projector psi1, b • projector (psi2 eps), (1 - p eps) • projector e]).trace = 1 := by
    constructor
    · apply blockDiagonal_psd
      intro f
      fin_cases f
      · exact (projector_psd _).smul ha
      · exact (projector_psd _).smul hb
      · exact (projector_psd _).smul hq
    · rw [Matrix.trace_blockDiagonal, Fin.sum_univ_three]
      change (a • projector psi1).trace + (b • projector (psi2 eps)).trace +
        ((1 - p eps) • projector e).trace = 1
      rw [trace_smul_projector _ psi1_unit,
        trace_smul_projector _ (psi2_unit eps he.le he'.le), trace_smul_projector _ e_unit,
        ← Complex.ofReal_add, ← Complex.ofReal_add, ht, Complex.ofReal_one]
  rw [Y0_eq eps he he', Y1_eq eps he he', shared_block_eq eps he]
  have hpHalf : 0 ≤ p eps / 2 := div_nonneg hp (by norm_num)
  refine ⟨hd _ _ hpHalf hpHalf (by ring), ?_⟩
  simpa only [zero_smul] using hd 0 (p eps) (by norm_num) hp (by ring)

/-- The positive-root argument of sqrt_dephase_sigma for weighted unit projectors. -/
private theorem sqrt_rankOne_blocks (v : Fin 3 → Fin 2 → ℂ) (a : Fin 3 → ℝ)
    (hv : ∀ f, star (v f) ⬝ᵥ v f = 1) (ha : ∀ f, 0 ≤ a f) :
    CFC.sqrt (Matrix.blockDiagonal (fun f => a f • projector (v f))) =
      Matrix.blockDiagonal (fun f => Real.sqrt (a f) • projector (v f)) := by
  apply CFC.sqrt_unique _
    (blockDiagonal_psd _ (fun f => (projector_psd _).smul (Real.sqrt_nonneg (a f)))).nonneg
  rw [← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext f
  change (Real.sqrt (a f) • projector (v f)) * (Real.sqrt (a f) • projector (v f)) =
    a f • projector (v f)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two (Real.sqrt (a f)),
    Real.sq_sqrt (ha f), projector_sq _ (hv f)]

private theorem rootFidelity_rankOne_blocks (v : Fin 3 → Fin 2 → ℂ) (a b : Fin 3 → ℝ)
    (hv : ∀ f, star (v f) ⬝ᵥ v f = 1) (ha : ∀ f, 0 ≤ a f) (hb : ∀ f, 0 ≤ b f) :
    rootFidelity (Matrix.blockDiagonal (fun f => a f • projector (v f)))
        (Matrix.blockDiagonal (fun f => b f • projector (v f))) =
      ∑ f : Fin 3, Real.sqrt (a f * b f) := by
  have hSandwich (f : Fin 3) :
      (Real.sqrt (a f) • projector (v f)) * (b f • projector (v f)) *
          (Real.sqrt (a f) • projector (v f)) = (a f * b f) • projector (v f) := by
    rw [smul_sandwich, ← pow_two (Real.sqrt (a f)), Real.sq_sqrt (ha f), Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, projector_sq _ (hv f), projector_sq _ (hv f)]
  rw [rootFidelity, sqrt_rankOne_blocks v a hv ha, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_mul, congrArg Matrix.blockDiagonal (funext hSandwich),
    sqrt_rankOne_blocks v (fun f => a f * b f) hv (fun f => mul_nonneg (ha f) (hb f)),
    Matrix.trace_blockDiagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [trace_smul_projector _ (hv f), Complex.ofReal_re]

/-- Exact quantum root fidelity of the transported and recomputed ordinary Petz outputs. -/
theorem rootFidelity_Y0_Y1 (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    rootFidelity (Y0 eps) (Y1 eps) = 1 - p eps + p eps * Real.sqrt (1 / 2) := by
  have hp := (p_pos eps he).le
  have hq : 0 ≤ 1 - p eps := by
    rw [← lambda_quarter eps he]
    exact div_nonneg (lambda_nonneg eps he) (by norm_num)
  let v : Fin 3 → Fin 2 → ℂ := ![psi1, psi2 eps, e]
  let a : Fin 3 → ℝ := ![p eps / 2, p eps / 2, 1 - p eps]
  let b : Fin 3 → ℝ := ![0, p eps, 1 - p eps]
  have hv (f : Fin 3) : star (v f) ⬝ᵥ v f = 1 := by
    fin_cases f
    · exact psi1_unit
    · exact psi2_unit eps he.le he'.le
    · exact e_unit
  have ha (f : Fin 3) : 0 ≤ a f := by
    fin_cases f
    · exact div_nonneg hp (by norm_num)
    · exact div_nonneg hp (by norm_num)
    · exact hq
  have hb (f : Fin 3) : 0 ≤ b f := by
    fin_cases f
    · exact le_rfl
    · exact hp
    · exact hq
  have hY0 : Y0 eps = Matrix.blockDiagonal (fun f => a f • projector (v f)) := by
    rw [Y0_eq eps he he', shared_block_eq eps he]
    apply congrArg Matrix.blockDiagonal
    funext f
    fin_cases f <;> rfl
  have hY1 : Y1 eps = Matrix.blockDiagonal (fun f => b f • projector (v f)) := by
    rw [Y1_eq eps he he', shared_block_eq eps he]
    apply congrArg Matrix.blockDiagonal
    funext f
    fin_cases f
    · exact (zero_smul ℝ (projector psi1)).symm
    · rfl
    · rfl
  rw [hY0, hY1, rootFidelity_rankOne_blocks v a b hv ha hb, Fin.sum_univ_three]
  change Real.sqrt (p eps / 2 * 0) + Real.sqrt (p eps / 2 * p eps) +
    Real.sqrt ((1 - p eps) * (1 - p eps)) = _
  rw [mul_zero, Real.sqrt_zero, zero_add, ← pow_two (1 - p eps), Real.sqrt_sq hq,
    show p eps / 2 * p eps = p eps ^ 2 * (1 / 2) by ring,
    Real.sqrt_mul (sq_nonneg (p eps)), Real.sqrt_sq hp, add_comm]

/-- The squared Bures distance in the trace-one convention. -/
theorem bures_sq_Y0_Y1 (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    2 * (1 - rootFidelity (Y0 eps) (Y1 eps)) =
      2 * p eps * (1 - Real.sqrt (1 / 2)) := by
  rw [rootFidelity_Y0_Y1 eps he he']
  ring

/-- The Bures square is a fixed positive multiple of the square root of the paired defect. -/
theorem bures_sq_eq_sqrt_Gamma (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    2 * (1 - rootFidelity (Y0 eps) (Y1 eps)) =
      (Real.sqrt 2 - 1) * Real.sqrt (Gamma eps) := by
  have hs : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_div_self']
  rw [bures_sq_Y0_Y1 eps he he', Gamma_eq eps he he', hs,
    show 2 * p eps ^ 2 = p eps ^ 2 * 2 by ring,
    Real.sqrt_mul (sq_nonneg (p eps)), Real.sqrt_sq (p_pos eps he).le]
  linear_combination -(p eps) * (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

/-- Reading flag 0 and guessing Y0 on that outcome attains the least equal-prior error. -/
theorem one_copy_label_test_optimal (eps : ℝ) (he : 0 < eps) (he' : eps < 1) :
    (0 ≤ flagProj 0 ∧ flagProj 0 ≤ 1) ∧
      ((1 - protectedProbability (Y0 eps) 0 + protectedProbability (Y1 eps) 0) / 2 =
        (1 - p eps / 2) / 2) ∧
      ∀ E : Joint, 0 ≤ E → E ≤ 1 →
        (1 - p eps / 2) / 2 ≤
          (1 - (E * Y0 eps).trace.re + (E * Y1 eps).trace.re) / 2 := by
  have hp : 0 ≤ p eps / 2 := div_nonneg (p_pos eps he).le (by norm_num)
  have hflag : flagProj 0 ≤ 1 := by
    rw [← flagProj_complete, Fin.sum_univ_three]
    exact (le_add_of_nonneg_right (flagProj_psd 1).nonneg).trans
      (le_add_of_nonneg_right (flagProj_psd 2).nonneg)
  have h0 := congrFun (protected_Y0 eps he he') (0 : Fin 3)
  have h1 := congrFun (protected_Y1 eps he he') (0 : Fin 3)
  change protectedProbability (Y0 eps) 0 = p eps / 2 at h0
  change protectedProbability (Y1 eps) 0 = 0 at h1
  refine ⟨⟨(flagProj_psd 0).nonneg, hflag⟩, ?_, ?_⟩
  · rw [h0, h1, add_zero]
  intro E hE hEone
  let U := atFlag 0 ((p eps / 2) • projector psi1)
  let V := atFlag 1 ((p eps / 2) • projector (psi2 eps))
  have atFlag_psd (f : Fin 3) (A : Qubit) (hA : A.PosSemidef) :
      (atFlag f A).PosSemidef := by
    unfold atFlag
    apply blockDiagonal_psd
    intro g
    by_cases h : g = f
    · simpa only [ite_eq_left h] using hA
    · rw [ite_eq_right h]
      exact Matrix.PosSemidef.zero
  have hU := atFlag_psd 0 _ ((projector_psd psi1).smul hp)
  have hV := atFlag_psd 1 _ ((projector_psd (psi2 eps)).smul hp)
  have hdiff : Y0 eps - Y1 eps = U - V := by
    dsimp only [U, V]
    rw [Y0_eq eps he he', Y1_eq eps he he', atFlag, atFlag,
      ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_sub]
    apply congrArg Matrix.blockDiagonal
    funext f
    fin_cases f
    · rfl
    · change (p eps / 2) • projector (psi2 eps) - p eps • projector (psi2 eps) =
        0 - (p eps / 2) • projector (psi2 eps)
      rw [zero_sub, ← sub_smul, ← neg_smul,
        show p eps / 2 - p eps = -(p eps / 2) by ring]
    · change (1 / 4 : ℝ) • M eps - (1 / 4 : ℝ) • M eps = (0 : Qubit) - 0
      simp only [sub_self]
  have hUtrace : U.trace.re = p eps / 2 := by
    dsimp only [U, atFlag]
    rw [Matrix.trace_blockDiagonal, Fin.sum_univ_three]
    change (((p eps / 2) • projector psi1).trace + (0 : Qubit).trace +
      (0 : Qubit).trace).re = _
    simp only [Matrix.trace_zero, add_zero, trace_smul_projector _ psi1_unit, Complex.ofReal_re]
  have hUV : 0 ≤ ((1 - E) * U).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hEone) hU
  rw [sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hUtrace] at hUV
  have hEV : 0 ≤ (E * V).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hE.posSemidef hV
  have hpair := congrArg (fun X : Joint => (E * X).trace.re) hdiff
  simp only [mul_sub, Matrix.trace_sub, Complex.sub_re] at hpair
  linarith only [hpair, hUV, hEV]

end D5.S3.Quantum.Recovery.LocalCompression.PetzCoherentErasureSharpPower
