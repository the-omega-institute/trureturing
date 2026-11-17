/- GID: D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HwangKimNearOrderRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.claim; result=D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.result; claim=D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.claim
   digest: The log-Euclidean mean need not precede the Wasserstein barycenter in near order. -/

/-
result proof_shape: bind-only (spectral calculus, variational duality and exact certificates).
escape_witness: none.
admission_basis: open-problem-resolution (#21282; Refuted).
Direct frozen dependencies (declaration statement_id; not module pins):
F1: D5/S0/Observation/MatrixTracePowerSum.pow_add_two
  sha256:477f52a1cada3768c6c6695f7bf1e92216cc53ac6f22ad3f67270f1f31f452be
F2: D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two
  sha256:c3a059dba6dacff2daf43a6483f3e2bb7036930561a43d038fdbb8225d03adff
F3: D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
  sha256:873e4955783786d99a250879f3da4640dab6550433b567150988ca3aaede9fe0
F4: D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
  sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059
F5: D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U
  sha256:3487611db943d93cce4a86af60f6499c8a001bc73fe819953d9bfd08a4e811b1
F6: D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.geometricMean
  sha256:bcc68a34d0f69b7d20fd56f1ddfa5a1c3dc9338c3ae7c9c80c2894bfe9cf15fe
F7: D5/S3/Quantum/Matrix/AlternativeMeanLinearization.gmInv
  sha256:485f301967ad92c67d9517ca9019d415c27d5d09269db36a8f792fa51fe66702
F8: D5/S3/Quantum/Matrix/AlternativeMeanLinearization.riccati
  sha256:57aa8048e63436772a51754a97319e30bead90eb9070acac3272303df4f878c9
F9: D5/S3/Quantum/Matrix/SpectralPower.mpow
  sha256:90a65cb357060c4a1a494f0fe9c2e62f452bd9f1f01bdbcbcb9cd8814fcc3216
F10: D5/S3/Quantum/Matrix/SpectralPower.posDef_two
  sha256:aab0c093aa3d2b2ec35e668b9050f590c2f79cbaf6d347b59632a1280bc73376
F11: D5/S3/Quantum/Matrix/GanKimConjectureRefutation.geometric_inverse
  sha256:127fdbd0e784b32ca5b05736130c1d266866bdb16a779bc8a427616048fe87f6
F12: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/ForMathlib/Isometry.cfc_conj_unitary
  sha256:673834744c358650a0ee4d02a874eff74ba463450baca922527751bc2237b97b
F13: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.trace_hermitian_product_real
  sha256:d57aafbe2afd1228c9b5e26bf06684ec80accc922d16f29290f16819337adc81
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The geometric mean uses its existing owner; the multivariable means use the source expressions. The functional-calculus conjugation helper applies `Matrix.cfc_conj_unitary`; the trace-reality helper applies `ProjectionProbabilityFlow.trace_hermitian_product_real`.
Per-declaration classification; definitions and concrete data carry no proof claim:
NearOrder: proof_shape=bind-only; frozen=F6; consumers=claim,result; escape_witness=none.
logEuclidean: proof_shape=bind-only; frozen=none; consumers=claim,logEuclidean_witness,result; escape_witness=none.
buresWassersteinDistance: proof_shape=bind-only; frozen=F9; consumers=wassersteinBarycenter,bures_sq,binaryObjective,binary_barycenter_of_dual; escape_witness=none.
wassersteinBarycenter: proof_shape=bind-only; frozen=F9; consumers=claim,binary_barycenter_of_dual,wasserstein_witness,result; escape_witness=none.
claim: proof_shape=bind-only; frozen=F6,F9; consumers=result; escape_witness=none.
rootU: proof_shape=bind-only; frozen=none; consumers=rootU_bounds,witnessL,exp_quarter_log_two,witnessL_spectral,logEuclidean_witness,witnessL_det,witnessL_pos,witnessL_trace,witnessLW_trace,witness_trace_test; escape_witness=none.
z: proof_shape=bind-only; frozen=none; consumers=rootZ_bounds,witnessK,witnessK_pos,witnessK_riccati,witnessD,witnessD_pos,witnessK_det,witnessK_trace,witnessW_det,witnessW_trace,witnessLW_trace,witness_trace_test; escape_witness=none.
rootU_bounds: proof_shape=bind-only; frozen=none; consumers=witnessL_spectral,witnessL_det,witnessL_pos,witnessLW_trace,witness_trace_test; escape_witness=none.
rootZ_bounds: proof_shape=bind-only; frozen=none; consumers=witness_trace_test; escape_witness=none.
g: proof_shape=bind-only; frozen=none; consumers=witnessB,witnessK,witnessB_pos,witnessK_pos,witnessK_riccati,rotationR,eigenV,witnessL,rotationR_unitary,eigenV_unitary,witnessB_diagonalization,logarithm_diagonalization,witnessL_spectral,witnessL_det,witnessK_det,witnessK_trace,witnessW_trace,witnessL_trace,witnessLW_trace; escape_witness=none.
witnessA: proof_shape=bind-only; frozen=none; consumers=witnessW,witnessK_riccati,witnessW_pos,log_witnessA,logarithm_diagonalization,logEuclidean_witness,witnessW_affine,witnessW_det,witnessW_trace,witnessLW_trace,wasserstein_witness,result; escape_witness=none.
witnessB: proof_shape=bind-only; frozen=none; consumers=witnessB_pos,witnessK_riccati,witnessB_diagonalization,log_witnessB,logarithm_diagonalization,logEuclidean_witness,witnessW_affine,witnessW_trace,witnessLW_trace,wasserstein_witness,result; escape_witness=none.
witnessK: proof_shape=bind-only; frozen=none; consumers=witnessW,witnessK_riccati,witnessW_pos,witnessW_affine,witnessK_det,witnessK_trace,witnessW_det,witnessW_trace,witnessLW_trace,wasserstein_witness; escape_witness=none.
witnessW: proof_shape=bind-only; frozen=none; consumers=witnessW_affine,witnessW_det,witnessW_trace,witnessLW_trace,witness_trace_test,wasserstein_witness,result; escape_witness=none.
witnessA_pos: proof_shape=bind-only; frozen=F10; consumers=witnessW_pos,wasserstein_witness,result; escape_witness=none.
witnessB_pos: proof_shape=bind-only; frozen=F10; consumers=result; escape_witness=none.
witnessK_pos: proof_shape=bind-only; frozen=F10; consumers=witnessW_pos,wasserstein_witness; escape_witness=none.
witnessK_riccati: proof_shape=bind-only; frozen=none; consumers=witnessW_affine,wasserstein_witness; escape_witness=none.
witnessW_pos: proof_shape=bind-only; frozen=F10; consumers=result; escape_witness=none.
fidelity_young_rigid: proof_shape=bind-only; frozen=F4,F5; consumers=bures_sq,binary_barycenter_of_dual; escape_witness=none.
fidelity_as_sqrt: proof_shape=bind-only; frozen=F4; consumers=bures_sq,fidelity_transport; escape_witness=none.
bures_sq: proof_shape=bind-only; frozen=F4,F5,F9; consumers=binary_barycenter_of_dual; escape_witness=none.
fidelity_transport: proof_shape=bind-only; frozen=F4; consumers=binary_barycenter_of_dual; escape_witness=none.
binaryObjective: proof_shape=bind-only; frozen=F9; consumers=binary_barycenter_of_dual; escape_witness=none.
binary_barycenter_of_dual: proof_shape=bind-only; frozen=F4,F5,F9; consumers=binary_midpoint_barycenter; escape_witness=none.
binary_midpoint_barycenter: proof_shape=bind-only; frozen=F4,F5,F9; consumers=wasserstein_witness; escape_witness=none.
rotationR: proof_shape=bind-only; frozen=none; consumers=rotationR_unitary,witnessB_diagonalization,log_witnessB,logarithm_diagonalization; escape_witness=none.
eigenV: proof_shape=bind-only; frozen=none; consumers=eigenV_unitary,logarithm_diagonalization,witnessL_spectral,logEuclidean_witness,witnessL_pos; escape_witness=none.
witnessL: proof_shape=bind-only; frozen=none; consumers=witnessL_spectral,logEuclidean_witness,witnessL_det,witnessL_pos,witnessL_trace,witnessLW_trace,witness_trace_test,result; escape_witness=none.
rotationR_unitary: proof_shape=bind-only; frozen=none; consumers=log_witnessB; escape_witness=none.
eigenV_unitary: proof_shape=bind-only; frozen=none; consumers=logEuclidean_witness,witnessL_pos; escape_witness=none.
witnessB_diagonalization: proof_shape=bind-only; frozen=none; consumers=log_witnessB; escape_witness=none.
cfc_conjugate_diagonal: proof_shape=bind-only; frozen=F3,F12; consumers=log_witnessB,logEuclidean_witness; escape_witness=none.
log_witnessA: proof_shape=bind-only; frozen=F3; consumers=logarithm_diagonalization; escape_witness=none.
log_witnessB: proof_shape=bind-only; frozen=F3; consumers=logarithm_diagonalization; escape_witness=none.
logarithm_diagonalization: proof_shape=bind-only; frozen=F3; consumers=logEuclidean_witness; escape_witness=none.
exp_quarter_log_two: proof_shape=bind-only; frozen=none; consumers=logEuclidean_witness; escape_witness=none.
witnessL_spectral: proof_shape=bind-only; frozen=none; consumers=logEuclidean_witness,witnessL_pos; escape_witness=none.
logEuclidean_witness: proof_shape=bind-only; frozen=F3; consumers=result; escape_witness=none.
trace_sign_by_intervals: proof_shape=bind-only; frozen=none; consumers=witness_trace_test; escape_witness=none.
trace_obstruction: proof_shape=bind-only; frozen=F1,F2,F13; consumers=result; escape_witness=none.
witnessD: proof_shape=bind-only; frozen=none; consumers=witnessD_pos,witnessW_det,witness_trace_test,result; escape_witness=none.
witnessD_pos: proof_shape=bind-only; frozen=none; consumers=result; escape_witness=none.
witnessL_det: proof_shape=bind-only; frozen=none; consumers=result; escape_witness=none.
witnessL_pos: proof_shape=bind-only; frozen=none; consumers=result; escape_witness=none.
witnessW_affine: proof_shape=bind-only; frozen=none; consumers=witnessW_trace,witnessLW_trace; escape_witness=none.
witnessK_det: proof_shape=bind-only; frozen=none; consumers=witnessW_det; escape_witness=none.
witnessK_trace: proof_shape=bind-only; frozen=none; consumers=witnessW_det; escape_witness=none.
witnessW_det: proof_shape=bind-only; frozen=none; consumers=result; escape_witness=none.
witnessW_trace: proof_shape=bind-only; frozen=none; consumers=witness_trace_test; escape_witness=none.
witnessL_trace: proof_shape=bind-only; frozen=none; consumers=witness_trace_test; escape_witness=none.
witnessLW_trace: proof_shape=bind-only; frozen=none; consumers=witness_trace_test; escape_witness=none.
witness_trace_test: proof_shape=bind-only; frozen=none; consumers=result; escape_witness=none.
nearOrder_riccati: proof_shape=bind-only; frozen=F6,F7,F8,F11; consumers=result; escape_witness=none.
wasserstein_witness: proof_shape=bind-only; frozen=F4,F5,F9,F10; consumers=result; escape_witness=none.
result: proof_shape=bind-only; frozen=F1,F2,F3,F4,F5,F6,F7,F8,F9,F10,F11; consumers=settling result; escape_witness=none.
-/

import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import D5.S3.Quantum.Matrix.GanKimConjectureRefutation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry


noncomputable section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Hiai.PsiMeanTraceConcavity (geometricMean)

/-- Equation (3.5): A ≼ B iff A⁻¹ # B ≥ I, with the existing geometric-mean owner. -/
def NearOrder {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (1 : Matrix (Fin m) (Fin m) ℂ) ≤ geometricMean (1 / 2) A⁻¹ B

/-- Equation (4.10): exp (∑ⱼ wⱼ log Aⱼ), using the same functional calculus as `SpectralPower.LE`. -/
def logEuclidean {m n : ℕ} (w : Fin n → ℝ)
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  cfc Real.exp (∑ j : Fin n, w j • cfc Real.log (A j))

/-- Section 2: d_W(A,B) = [tr(A+B) − 2 tr((A^(1/2) B A^(1/2))^(1/2))]^(1/2). -/
def buresWassersteinDistance {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  Real.sqrt ((Matrix.trace (A + B)).re -
    2 * (Matrix.trace (mpow (mpow A (1 / 2) * B * mpow A (1 / 2)) (1 / 2))).re)

/-- Section 4: Ω is the least-squares mean for the Bures–Wasserstein distance.
The source states that the positive-definite minimizer exists uniquely for admissible inputs. -/
def wassersteinBarycenter {m n : ℕ} (w : Fin n → ℝ)
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Classical.epsilon (fun X : Matrix (Fin m) (Fin m) ℂ =>
    X.PosDef ∧ ∀ Y : Matrix (Fin m) (Fin m) ℂ, Y.PosDef →
      (∑ j : Fin n, w j * buresWassersteinDistance X (A j) ^ 2) ≤
        ∑ j : Fin n, w j * buresWassersteinDistance Y (A j) ^ 2)

/-- Hwang–Kim, arXiv:2407.07438v1, §6, final unnumbered open inequality.
No restriction to two inputs or to real matrices is imposed. -/
def claim : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (n : ℕ), 2 ≤ n →
    ∀ (w : Fin n → ℝ), (∀ j : Fin n, 0 < w j) →
      (∑ j : Fin n, w j) = 1 →
    ∀ (A : Fin n → Matrix (Fin m) (Fin m) ℂ),
      (∀ j : Fin n, (A j).PosDef) →
      NearOrder (logEuclidean w A) (wassersteinBarycenter w A)

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation


noncomputable section
namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

private def rootU : ℝ := Real.sqrt (Real.sqrt 2)
private def z : ℝ := Real.sqrt 265

private theorem rootU_bounds :
    (1189207115002721 : ℝ) / 10^15 < rootU ∧
      rootU < (1189207115002722 : ℝ) / 10^15 := by
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h22 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hu : 0 ≤ rootU := Real.sqrt_nonneg _
  have huu : rootU^2 = Real.sqrt 2 := Real.sq_sqrt h2
  constructor
  · by_contra h
    have hle : rootU ≤ (1189207115002721 : ℝ) / 10^15 := le_of_not_gt h
    have hsq : rootU^2 ≤ ((1189207115002721 : ℝ) / 10^15)^2 :=
      pow_le_pow_left₀ hu hle 2
    rw [huu] at hsq
    have hsq2 := pow_le_pow_left₀ h2 hsq 2
    norm_num [h22] at hsq2
  · by_contra h
    have hle : (1189207115002722 : ℝ) / 10^15 ≤ rootU := le_of_not_gt h
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1189207115002722 / 10^15) hle 2
    rw [huu] at hsq
    have hsq2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1189207115002722 / 10^15)^2) hsq 2
    norm_num [h22] at hsq2

private theorem rootZ_bounds :
    (16278820596099706 : ℝ) / 10^15 < z ∧
      z < (16278820596099707 : ℝ) / 10^15 := by
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hzz : z^2 = 265 := Real.sq_sqrt (by norm_num)
  constructor
  · by_contra h
    have hle : z ≤ (16278820596099706 : ℝ) / 10^15 := le_of_not_gt h
    have hsq := pow_le_pow_left₀ hz hle 2
    norm_num at hsq
    nlinarith only [hsq,hzz]
  · by_contra h
    have hle : (16278820596099707 : ℝ) / 10^15 ≤ z := le_of_not_gt h
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16278820596099707 / 10^15) hle 2
    norm_num at hsq
    nlinarith only [hsq,hzz]

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation


noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

private def g : ℝ := Real.sqrt 15

private def witnessA : (Matrix (Fin 2) (Fin 2) ℂ) := !![4, 0; 0, 1]
private def witnessB : (Matrix (Fin 2) (Fin 2) ℂ) :=
  !![((19 : ℝ)/64 : ℂ), ((-3*g/64 : ℝ) : ℂ);
     ((-3*g/64 : ℝ) : ℂ), ((61 : ℝ)/64 : ℂ)]
private def witnessK : (Matrix (Fin 2) (Fin 2) ℂ) :=
  !![((35/(8*z) : ℝ) : ℂ), ((-3*g/(8*z) : ℝ) : ℂ);
     ((-3*g/(8*z) : ℝ) : ℂ), ((125/(8*z) : ℝ) : ℂ)]
private def witnessW : (Matrix (Fin 2) (Fin 2) ℂ) := (1/4 : ℝ) • ((1+witnessK) * witnessA * (1+witnessK))

private theorem witnessA_pos : witnessA.PosDef := by
  exact D5.S3.Quantum.Matrix.SpectralPower.posDef_two 4 0 1 (by norm_num) (by norm_num)

private theorem witnessB_pos : witnessB.PosDef := by
  have hg : g^2 = 15 := Real.sq_sqrt (by norm_num)
  have h := D5.S3.Quantum.Matrix.SpectralPower.posDef_two (19/64) (-3*g/64) (61/64)
    (by norm_num) (by nlinarith [hg])
  simpa [witnessB,Complex.ofReal_div] using h

private theorem witnessK_pos : witnessK.PosDef := by
  have hz : 0 < z := Real.sqrt_pos.mpr (by norm_num)
  have hg : g^2 = 15 := Real.sq_sqrt (by norm_num)
  apply D5.S3.Quantum.Matrix.SpectralPower.posDef_two (35/(8*z)) (-3*g/(8*z)) (125/(8*z))
  · positivity
  · have hN : (0 : ℝ) < 35*125-(-3*g)^2 := by nlinarith [hg]
    convert div_pos hN (sq_pos_of_pos (show 0 < 8*z by positivity)) using 1 <;>
      field_simp <;> ring

private theorem witnessK_riccati : witnessK * witnessA * witnessK = witnessB := by
  have hz : z ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hg : g^2 = 15 := Real.sq_sqrt (by norm_num)
  have hzz : z^2 = 265 := Real.sq_sqrt (by norm_num)
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  have hgC : (g : ℂ)^2 = 15 := by exact_mod_cast hg
  have hzzC : (z : ℂ)^2 = 265 := by exact_mod_cast hzz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessK,witnessA,witnessB,Matrix.mul_apply,Fin.sum_univ_two,
      Complex.ofReal_div,Complex.ofReal_mul] <;>
    field_simp [hzC] <;> ring_nf <;> simp only [hgC,hzzC] <;> ring

private theorem witnessW_pos : witnessW.PosDef := by
  have hI : (1+witnessK).PosDef := Matrix.PosDef.one.add witnessK_pos
  have hc : ((1+witnessK) * witnessA * (1+witnessK)).PosDef := by
    simpa only [star_eq_conjTranspose,hI.isHermitian.eq] using
      hI.isUnit.posDef_star_right_conjugate_iff.mpr witnessA_pos
  exact hc.smul (by norm_num)

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation


noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open D5.S3.Quantum.Foundation.FiniteTraceDistance
variable {n : Type*} [Fintype n] [DecidableEq n]


private theorem fidelity_young_rigid {X A T : Matrix n n ℂ}
    (hX : X.PosDef) (hA : A.PosDef) (hT : T.PosDef) :
    2 * traceNorm (CFC.sqrt A * CFC.sqrt X) ≤
      (T*X).trace.re + (T⁻¹*A).trace.re ∧
    (2 * traceNorm (CFC.sqrt A * CFC.sqrt X) =
      (T*X).trace.re + (T⁻¹*A).trace.re → T*X*T = A) := by
  let S := CFC.rpow T (1/2 : ℝ)
  let R := CFC.rpow T (-1/2 : ℝ)
  have hS : Sᴴ = S := (hT.isStrictlyPositive.rpow T (1/2)).isSelfAdjoint.star_eq
  have hR : Rᴴ = R := (hT.isStrictlyPositive.rpow T (-1/2)).isSelfAdjoint.star_eq
  have hSX : (CFC.sqrt X)ᴴ = CFC.sqrt X := (hX.isStrictlyPositive.sqrt).isSelfAdjoint.star_eq
  have hSA : (CFC.sqrt A)ᴴ = CFC.sqrt A := (hA.isStrictlyPositive.sqrt).isSelfAdjoint.star_eq
  have hXX : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg
  have hAA : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSR : S*R = 1 := by
    simpa [S,R,neg_div] using CFC.rpow_mul_rpow_neg (a := T) (1/2 : ℝ) hT.isStrictlyPositive
  have hRS : R*S = 1 := by
    simpa [S,R,neg_div] using CFC.rpow_neg_mul_rpow (a := T) (1/2 : ℝ) hT.isStrictlyPositive
  have hSS : S*S = T := by
    dsimp [S]
    rw [← CFC.rpow_add hT.isUnit]
    norm_num
    exact CFC.rpow_one T hT.posSemidef.nonneg
  have hRR : R*R = T⁻¹ := by
    dsimp [R]
    rw [← CFC.rpow_add hT.isUnit]
    norm_num
    exact ((Matrix.nonsing_inv_eq_ringInverse (A := T)).trans
      (CFC.inverse_eq_rpow_neg_one hT.isStrictlyPositive)).symm
  obtain ⟨U,hU⟩ := (traceNorm_eq_max_re_tr_U (CFC.sqrt A * CFC.sqrt X)).1
  have hUU : U.valᴴ * U.val = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.property
  let P := CFC.sqrt X * S
  let Q := U.val * CFC.sqrt A * R
  let E := P-Q
  have hPP : (Pᴴ*P).trace = (T*X).trace := by
    have hp : Pᴴ*P = S*X*S := by
      simp only [P,Matrix.conjTranspose_mul,hS,hSX]
      calc
        _ = S*(CFC.sqrt X*CFC.sqrt X)*S := by noncomm_ring
        _ = S*X*S := by rw [hXX]
    rw [hp,Matrix.trace_mul_cycle, hSS]
  have hQQ : (Qᴴ*Q).trace = (T⁻¹*A).trace := by
    have hq : Qᴴ*Q = R*A*R := by
      simp only [Q,Matrix.conjTranspose_mul,hR,hSA]
      calc
        _ = R*CFC.sqrt A*(U.valᴴ*U.val)*CFC.sqrt A*R := by noncomm_ring
        _ = R*(CFC.sqrt A*CFC.sqrt A)*R := by rw [hUU]; noncomm_ring
        _ = R*A*R := by rw [hAA]
    rw [hq,Matrix.trace_mul_cycle,hRR]
  have hPQ : (Pᴴ*Q).trace = (U.val*(CFC.sqrt A*CFC.sqrt X)).trace := by
    have hpq : Pᴴ*Q = S*(CFC.sqrt X*U.val*CFC.sqrt A)*R := by
      simp only [P,Q,Matrix.conjTranspose_mul,hS,hSX]
      noncomm_ring
    rw [hpq,Matrix.trace_mul_cycle,hRS,one_mul]
    rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm (CFC.sqrt A*CFC.sqrt X) U.val]
  have hQP : (Qᴴ*P).trace.re = (Pᴴ*Q).trace.re := by
    have hc : Qᴴ*P = (Pᴴ*Q)ᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    rw [hc,Matrix.trace_conjTranspose]
    rfl
  have hE : (Eᴴ*E).trace.re = (T*X).trace.re + (T⁻¹*A).trace.re -
      2 * traceNorm (CFC.sqrt A*CFC.sqrt X) := by
    have he : Eᴴ*E = Pᴴ*P-Pᴴ*Q-Qᴴ*P+Qᴴ*Q := by
      simp only [E,Matrix.conjTranspose_sub]
      noncomm_ring
    rw [he,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_sub]
    simp only [Complex.add_re,Complex.sub_re,hPP,hQQ,hQP,hPQ,hU]
    ring
  have hnonneg := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self E).trace_nonneg).1
  refine ⟨by linarith, ?_⟩
  intro heq
  have he0 : (Eᴴ*E).trace.re = 0 := by linarith
  have heim := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self E).trace_nonneg).2
  have heM : E = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (Complex.ext he0 heim.symm)
  have hpq : P = Q := sub_eq_zero.mp heM
  have hx : CFC.sqrt X*T = U.val*CFC.sqrt A := by
    have hh := congrArg (fun Z : Matrix n n ℂ => Z*S) hpq
    dsimp [P,Q] at hh
    calc
      CFC.sqrt X*T = (CFC.sqrt X*S)*S := by rw [mul_assoc,hSS]
      _ = (U.val*CFC.sqrt A*R)*S := hh
      _ = U.val*CFC.sqrt A := by rw [mul_assoc,hRS,mul_one]
  have hXT : (CFC.sqrt X*T)ᴴ*(CFC.sqrt X*T) = T*X*T := by
    simp only [Matrix.conjTranspose_mul,hT.isHermitian.eq,hSX]
    calc
      _ = T*(CFC.sqrt X*CFC.sqrt X)*T := by noncomm_ring
      _ = T*X*T := by rw [hXX]
  rw [← hXT,hx,Matrix.conjTranspose_mul,hSA]
  calc
    _ = CFC.sqrt A*(U.valᴴ*U.val)*CFC.sqrt A := by noncomm_ring
    _ = A := by rw [hUU]; simpa only [mul_one] using hAA

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
variable {m : ℕ}


private theorem fidelity_as_sqrt {X A : Matrix (Fin m) (Fin m) ℂ}
    (hX : X.PosDef) (hA : A.PosDef) :
    traceNorm (CFC.sqrt A * CFC.sqrt X) = (CFC.sqrt (CFC.sqrt X * A * CFC.sqrt X)).trace.re := by
  have hSX : (CFC.sqrt X)ᴴ = CFC.sqrt X := hX.isStrictlyPositive.sqrt.isSelfAdjoint.star_eq
  have hSA : (CFC.sqrt A)ᴴ = CFC.sqrt A := hA.isStrictlyPositive.sqrt.isSelfAdjoint.star_eq
  have hAA := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  unfold traceNorm
  rw [Matrix.conjTranspose_mul,hSX,hSA]
  have he : (CFC.sqrt X*CFC.sqrt A)*(CFC.sqrt A*CFC.sqrt X) =
      CFC.sqrt X*A*CFC.sqrt X := by
    calc
      _ = CFC.sqrt X*(CFC.sqrt A*CFC.sqrt A)*CFC.sqrt X := by noncomm_ring
      _ = _ := by rw [hAA]
  rw [he]
  rfl

private theorem bures_sq {X A : Matrix (Fin m) (Fin m) ℂ}
    (hX : X.PosDef) (hA : A.PosDef) :
    buresWassersteinDistance X A ^ 2 = X.trace.re + A.trace.re - 2*traceNorm (CFC.sqrt A * CFC.sqrt X) := by
  have hx : mpow X (1/2) = CFC.sqrt X := by
    rw [mpow,← CFC.rpow_eq_cfc_real hX.posSemidef.nonneg,← CFC.sqrt_eq_rpow]
  have hS : (CFC.sqrt X).PosDef := hX.isStrictlyPositive.sqrt.posDef
  have hM : (CFC.sqrt X*A*CFC.sqrt X).PosDef := by
    simpa only [star_eq_conjTranspose,hS.isHermitian.eq] using
      hS.isUnit.posDef_star_right_conjugate_iff.mpr hA
  have hm : mpow (CFC.sqrt X*A*CFC.sqrt X) (1/2) =
      CFC.sqrt (CFC.sqrt X*A*CFC.sqrt X) := by
    rw [mpow,← CFC.rpow_eq_cfc_real hM.posSemidef.nonneg,← CFC.sqrt_eq_rpow]
  have hn := (fidelity_young_rigid hX hA Matrix.PosDef.one).1
  simp only [one_mul,inv_one] at hn
  change 2*traceNorm (CFC.sqrt A * CFC.sqrt X) ≤ X.trace.re+A.trace.re at hn
  unfold buresWassersteinDistance
  rw [hx,hm,Matrix.trace_add,Complex.add_re,← fidelity_as_sqrt hX hA,
    Real.sq_sqrt (by linarith)]

private theorem fidelity_transport {W A T : Matrix (Fin m) (Fin m) ℂ}
    (hW : W.PosDef) (hA : A.PosDef) (hT : T.PosDef) (h : T*W*T=A) :
    traceNorm (CFC.sqrt A * CFC.sqrt W) = (T*W).trace.re ∧ (T⁻¹*A).trace.re = (T*W).trace.re := by
  let S := CFC.sqrt W
  have hS : S.PosDef := hW.isStrictlyPositive.sqrt.posDef
  have hSS : S*S=W := CFC.sqrt_mul_sqrt_self W hW.posSemidef.nonneg
  have hH : (S*T*S).PosDef := by
    simpa only [star_eq_conjTranspose,hS.isHermitian.eq] using
      hS.isUnit.posDef_star_right_conjugate_iff.mpr hT
  have he : S*T*S*(S*T*S) = S*A*S := by
    calc
      _ = S*(T*(S*S)*T)*S := by noncomm_ring
      _ = S*A*S := by rw [hSS,h]
  have hsqrt : CFC.sqrt (S*A*S) = S*T*S := CFC.sqrt_unique he hH.posSemidef.nonneg
  have hi : T⁻¹*T=1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
  constructor
  · rw [fidelity_as_sqrt hW hA]
    change (CFC.sqrt (S*A*S)).trace.re = _
    rw [hsqrt,Matrix.trace_mul_cycle,hSS,Matrix.trace_mul_comm]
  · rw [← h,← mul_assoc,← mul_assoc,hi,one_mul,Matrix.trace_mul_comm]

private def binaryObjective (A B X : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  (buresWassersteinDistance X A ^ 2 + buresWassersteinDistance X B ^ 2)/2

private theorem binary_barycenter_of_dual {A B W T V : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hW : W.PosDef) (hT : T.PosDef) (hV : V.PosDef)
    (hTW : T*W*T=A) (hVW : V*W*V=B) (hTV : T+V=(2:ℝ) • 1) :
    wassersteinBarycenter (fun _ : Fin 2 => (1/2 : ℝ)) ![A,B] = W := by
  have hFT := fidelity_transport hW hA hT hTW
  have hFV := fidelity_transport hW hB hV hVW
  have hsum (X : Matrix (Fin m) (Fin m) ℂ) :
      (T*X).trace.re+(V*X).trace.re=2*X.trace.re := by
    rw [← Complex.add_re,← Matrix.trace_add,← add_mul,hTV,smul_mul_assoc,one_mul,
      Matrix.trace_smul]
    simp [Complex.smul_re]
  have obj (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef) :
      binaryObjective A B X = X.trace.re+(A.trace.re+B.trace.re)/2-traceNorm (CFC.sqrt A * CFC.sqrt X)-traceNorm (CFC.sqrt B * CFC.sqrt X) := by
    rw [binaryObjective,bures_sq hX hA,bures_sq hX hB]
    ring
  have hmin (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef) :
      binaryObjective A B W ≤ binaryObjective A B X := by
    have ht := (fidelity_young_rigid hX hA hT).1
    have hv := (fidelity_young_rigid hX hB hV).1
    change 2*traceNorm (CFC.sqrt A * CFC.sqrt X) ≤ _ at ht
    change 2*traceNorm (CFC.sqrt B * CFC.sqrt X) ≤ _ at hv
    rw [obj W hW,obj X hX,hFT.1,hFV.1]
    rw [hFT.2] at ht
    rw [hFV.2] at hv
    linarith [hsum W,hsum X]
  have hunique (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef)
      (hx : binaryObjective A B X ≤ binaryObjective A B W) : X=W := by
    have ht := fidelity_young_rigid hX hA hT
    have hv := (fidelity_young_rigid hX hB hV).1
    have heq : 2*traceNorm (CFC.sqrt A * CFC.sqrt X)=(T*X).trace.re+(T⁻¹*A).trace.re := by
      rw [obj X hX,obj W hW,hFT.1,hFV.1] at hx
      change 2*traceNorm (CFC.sqrt B * CFC.sqrt X) ≤ _ at hv
      have ht0 := ht.1
      change 2*traceNorm (CFC.sqrt A * CFC.sqrt X) ≤ _ at ht0
      rw [hFT.2] at ht0
      rw [hFV.2] at hv
      linarith [hsum W,hsum X]
    have htx := ht.2 heq
    have hleft : T*X*T=T*W*T := htx.trans hTW.symm
    have hi : T⁻¹*T=1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
    have hi' : T*T⁻¹=1 := Matrix.mul_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
    have hh := congrArg (fun Z : Matrix (Fin m) (Fin m) ℂ => T⁻¹*Z*T⁻¹) hleft
    have hcancel (Z : Matrix (Fin m) (Fin m) ℂ) : T⁻¹*(T*Z*T)*T⁻¹=Z := by
      calc
        _ = (T⁻¹*T)*Z*(T*T⁻¹) := by noncomm_ring
        _ = Z := by rw [hi,hi']; simp
    exact (hcancel X).symm.trans (hh.trans (hcancel W))
  let pred := fun X : Matrix (Fin m) (Fin m) ℂ => X.PosDef ∧
    ∀ Y : Matrix (Fin m) (Fin m) ℂ, Y.PosDef → binaryObjective A B X ≤ binaryObjective A B Y
  have hp : ∃ X, pred X := ⟨W,hW,hmin⟩
  have heps : pred (Classical.epsilon pred) := Classical.epsilon_spec hp
  have he : Classical.epsilon pred=W := hunique _ heps.1 (heps.2 W hW)
  have hobj (X : Matrix (Fin m) (Fin m) ℂ) :
      (∑ j : Fin 2, (1/2:ℝ)*buresWassersteinDistance X (![A,B] j)^2)=binaryObjective A B X := by
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,binaryObjective]
    ring
  have hsel : wassersteinBarycenter (fun _ : Fin 2 => (1/2:ℝ)) ![A,B] = Classical.epsilon pred := by
    unfold wassersteinBarycenter
    congr 1
    funext X
    simp only [hobj,pred]
  exact hsel.trans he

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
variable {m : ℕ}

private theorem binary_midpoint_barycenter {A K : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hK : K.PosDef) :
    wassersteinBarycenter (fun _ : Fin 2 => (1/2:ℝ)) ![A,K*A*K] =
      ((1/2:ℝ) • (1+K)) * A * ((1/2:ℝ) • (1+K)) := by
  let M := (1/2:ℝ) • (1+K)
  let T := M⁻¹
  let V := K*T
  let W := M*A*M
  have hM : M.PosDef := (Matrix.PosDef.one.add hK).smul (by norm_num)
  have hT : T.PosDef := hM.inv
  have hTM : T*M=1 := Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit)
  have hMT : M*T=1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit)
  have hKexpr : K=(2:ℝ) • M-1 := by dsimp [M]; module
  have hKT : Commute K T := by
    change K*T=T*K
    rw [hKexpr]
    simp only [sub_mul,mul_sub,smul_mul_assoc,Matrix.mul_smul,hTM,hMT,one_mul,mul_one]
  have hV : V.PosDef := ((hK.isStrictlyPositive.commute_iff hT.isStrictlyPositive).1 hKT).posDef
  have hW : W.PosDef := by
    simpa only [W,star_eq_conjTranspose,hM.isHermitian.eq] using
      hM.isUnit.posDef_star_right_conjugate_iff.mpr hA
  have hB : (K*A*K).PosDef := by
    simpa only [star_eq_conjTranspose,hK.isHermitian.eq] using
      hK.isUnit.posDef_star_right_conjugate_iff.mpr hA
  have hTW : T*W*T=A := by
    dsimp [W]
    calc
      _ = (T*M)*A*(M*T) := by noncomm_ring
      _ = A := by rw [hTM,hMT]; simp
  have hVW : V*W*V=K*A*K := by
    change K*T*(M*A*M)*(K*T)=K*A*K
    calc
      _ = K*T*(M*A*M)*(T*K) := congrArg (fun Z => K*T*(M*A*M)*Z) hKT.eq
      _ = K*(T*M)*A*(M*T)*K := by noncomm_ring
      _ = K*A*K := by rw [hTM,hMT]; simp
  have hTV : T+V=(2:ℝ) • 1 := by
    dsimp [V]
    rw [hKexpr]
    simp only [sub_mul,smul_mul_assoc,hMT,one_mul]
    abel
  exact binary_barycenter_of_dual hA hB hW hT hV hTW hVW hTV

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation


namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

private def rotationR : (Matrix (Fin 2) (Fin 2) ℂ) := !![((g/4:ℝ):ℂ), -1/4; 1/4, ((g/4:ℝ):ℂ)]
private def eigenV : (Matrix (Fin 2) (Fin 2) ℂ) :=
  !![((g/Real.sqrt 24:ℝ):ℂ), ((3/Real.sqrt 24:ℝ):ℂ);
     ((-3/Real.sqrt 24:ℝ):ℂ), ((g/Real.sqrt 24:ℝ):ℂ)]
private def witnessL : (Matrix (Fin 2) (Fin 2) ℂ) :=
  !![(((5*rootU+3/rootU)/8:ℝ):ℂ), ((-g*(rootU-1/rootU)/8:ℝ):ℂ);
     ((-g*(rootU-1/rootU)/8:ℝ):ℂ), (((3*rootU+5/rootU)/8:ℝ):ℂ)]

private theorem rotationR_unitary : rotationR ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hg : (g:ℂ)^2=15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤15))
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationR,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply,map_ofNat,
      Complex.ofReal_div] <;> (try ring_nf) <;> (try simp only [hg]) <;> ring

private theorem eigenV_unitary : eigenV ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hg : (g:ℂ)^2=15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤15))
  have ht : ((Real.sqrt 24:ℝ):ℂ)^2=24 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤24))
  have ht0 : ((Real.sqrt 24:ℝ):ℂ)≠0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<24))
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenV,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply,map_ofNat,
      Complex.ofReal_div] <;> field_simp [ht0] <;> (try ring_nf) <;> (try simp only [hg,ht]) <;> ring

private theorem witnessB_diagonalization : witnessB = rotationR * diagonal ![(1/4:ℂ),1] * rotationRᴴ := by
  have hg : (g:ℂ)^2=15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤15))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessB,rotationR,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply,map_ofNat,
      Matrix.diagonal_apply,Complex.ofReal_div,Complex.ofReal_mul] <;>
    ring_nf <;> (try simp only [hg]) <;> ring

private theorem cfc_conjugate_diagonal (f : ℝ → ℝ) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (d : Fin 2 → ℝ) :
    cfc f (U.val * diagonal (fun i => (d i:ℂ)) * U.valᴴ) =
      U.val * diagonal (fun i => (f (d i):ℂ)) * U.valᴴ := by
  let D : (Matrix (Fin 2) (Fin 2) ℂ) := diagonal (fun i => (d i:ℂ))
  have hcfc := Matrix.cfc_conj_unitary (A := D) f U
  have hcfcD : cfc f D = diagonal (fun i => (f (d i):ℂ)) := by
    change cfc f (diagonal (fun i => (d i:ℂ))) = _
    rw [D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
  rw [show U.val * diagonal (fun i => (d i:ℂ)) * U.valᴴ = U.val * D * U.valᴴ by rfl]
  have hUinv : (↑(U⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) = U.valᴴ := by
    rfl
  rw [hUinv] at hcfc
  rw [hcfc]
  rw [hcfcD]

private theorem log_witnessA : cfc Real.log witnessA = diagonal ![((2*Real.log 2:ℝ):ℂ),0] := by
  have ha : witnessA=diagonal (fun i => ((![4,1]:Fin 2 → ℝ) i:ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessA,Matrix.diagonal_apply]
  rw [ha,D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
  have hl : Real.log 4=2*Real.log 2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] using Real.log_pow (2:ℝ) 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hl]

private theorem log_witnessB : cfc Real.log witnessB =
    rotationR * diagonal ![((-2*Real.log 2:ℝ):ℂ),0] * rotationRᴴ := by
  rw [witnessB_diagonalization]
  have he : diagonal ![(1/4:ℂ),1]=diagonal (fun i => ((![1/4,1]:Fin 2 → ℝ) i:ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]
  rw [he,cfc_conjugate_diagonal Real.log ⟨rotationR,rotationR_unitary⟩]
  have hl : Real.log (1/4:ℝ)=-2*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one]
    have h4 := Real.log_pow (2:ℝ) 2
    norm_num at h4
    linarith
  have hd : (fun i : Fin 2 => (Real.log ((![1/4,1] : Fin 2 → ℝ) i) : ℂ)) =
      ![((-2*Real.log 2:ℝ):ℂ),0] := by
    funext i
    fin_cases i
    · change ((Real.log (1/4:ℝ):ℝ):ℂ)=((-2*Real.log 2:ℝ):ℂ)
      rw [hl]
    · change ((Real.log (1:ℝ):ℝ):ℂ)=0
      rw [Real.log_one]
      rfl
  rw [hd]

private theorem logarithm_diagonalization :
    (1/2:ℝ) • cfc Real.log witnessA + (1/2:ℝ) • cfc Real.log witnessB =
      eigenV * diagonal ![((Real.log 2/4:ℝ):ℂ), ((-Real.log 2/4:ℝ):ℂ)] * eigenVᴴ := by
  have hg : (g:ℂ)^2=15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤15))
  have ht : ((Real.sqrt 24:ℝ):ℂ)^2=24 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤24))
  have ht0 : ((Real.sqrt 24:ℝ):ℂ)≠0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<24))
  rw [log_witnessA,log_witnessB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenV,rotationR,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply,map_ofNat,
      Matrix.diagonal_apply,Complex.ofReal_div,Complex.ofReal_mul,Complex.real_smul] <;>
    field_simp [ht0] <;> (try ring_nf) <;> (try simp only [hg,ht]) <;> ring

private theorem exp_quarter_log_two : Real.exp (Real.log 2/4)=rootU := by
  unfold rootU
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul (by norm_num : (0:ℝ)≤2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

private theorem witnessL_spectral : witnessL = eigenV * diagonal ![(rootU:ℂ),((1/rootU:ℝ):ℂ)] * eigenVᴴ := by
  have hg : (g:ℂ)^2=15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤15))
  have ht : ((Real.sqrt 24:ℝ):ℂ)^2=24 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤24))
  have ht0 : ((Real.sqrt 24:ℝ):ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<24))
  have hu0 : (rootU:ℂ)≠0 := by exact_mod_cast ne_of_gt (lt_trans (by norm_num) rootU_bounds.1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessL,eigenV,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply,map_ofNat,
      Matrix.diagonal_apply,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub] <;>
    field_simp [ht0,hu0] <;> (try ring_nf) <;> (try simp only [hg,ht]) <;> ring

private theorem logEuclidean_witness : logEuclidean (fun _ : Fin 2 => (1/2:ℝ)) ![witnessA,witnessB]=witnessL := by
  simp only [logEuclidean,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [logarithm_diagonalization]
  have he : diagonal ![((Real.log 2/4:ℝ):ℂ),((-Real.log 2/4:ℝ):ℂ)] =
      diagonal (fun i => ((![Real.log 2/4,-Real.log 2/4]:Fin 2 → ℝ) i:ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  rw [he,cfc_conjugate_diagonal Real.exp ⟨eigenV,eigenV_unitary⟩,witnessL_spectral]
  have hneg : Real.exp (-Real.log 2/4)=1/rootU := by
    rw [neg_div,Real.exp_neg,exp_quarter_log_two,one_div]
  have hd : (fun i : Fin 2 => (Real.exp ((![Real.log 2/4,-Real.log 2/4] : Fin 2 → ℝ) i) : ℂ)) =
      ![(rootU:ℂ),((1/rootU:ℝ):ℂ)] := by
    funext i
    fin_cases i
    · change (Real.exp (Real.log 2/4):ℂ)=(rootU:ℂ)
      rw [exp_quarter_log_two]
    · change (Real.exp (-Real.log 2/4):ℂ)=((1/rootU:ℝ):ℂ)
      rw [hneg]
  rw [hd]

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation


namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

private theorem trace_sign_by_intervals {u z : ℝ}
    (hu0 : (1189207115002721:ℝ)/10^15 < u)
    (hu1 : u < (1189207115002722:ℝ)/10^15)
    (hz0 : (16278820596099706:ℝ)/10^15 < z)
    (hz1 : z < (16278820596099707:ℝ)/10^15) :
    (3/2500:ℝ) < ((25/16:ℝ)+265/(16*z)+(5/8+10/z)*(u+1/u))^2-
      (1+(5/8+10/z))^2*(115*u/128+325*u/(32*z)+85/(128*u)+205/(32*u*z)+2*(5/8+10/z)) := by
  have hu : 0<u := lt_trans (by norm_num) hu0
  have hz : 0<z := lt_trans (by norm_num) hz0
  calc
    (3/2500:ℝ) < ((25/16:ℝ)+265/(16*(16278820596099707/10^15:ℝ))+(5/8+10/(16278820596099707/10^15:ℝ))*((1189207115002721/10^15:ℝ)+1/(1189207115002722/10^15:ℝ)))^2-(1+(5/8+10/(16278820596099706/10^15:ℝ)))^2*(115*(1189207115002722/10^15:ℝ)/128+325*(1189207115002722/10^15:ℝ)/(32*(16278820596099706/10^15:ℝ))+85/(128*(1189207115002721/10^15:ℝ))+205/(32*(1189207115002721/10^15:ℝ)*(16278820596099706/10^15:ℝ))+2*(5/8+10/(16278820596099706/10^15:ℝ))) := by norm_num
    _ ≤ _ := by
      gcongr <;> first | assumption | linarith | positivity

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation


noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

private theorem transport_trace_identities {L W C : (Matrix (Fin 2) (Fin 2) ℂ)} {d : ℝ}
    (hL : L.PosDef) (hC : C.PosDef)
    (hd : 0 < d) (hdetL : L.det=1) (hdetW : W.det=(d^2:ℝ))
    (hCL : C*L*C=W)
    : C.det = (d : ℂ) ∧
      W.trace.re + d * L.trace.re = (L*C).trace.re * C.trace.re ∧
      (L*W).trace.re + 2*d = (L*C).trace.re^2 := by
  have hci : C.det.im=0 := (Complex.nonneg_iff.mp hC.posSemidef.det_nonneg).2.symm
  have hcr : 0 ≤ C.det.re := (Complex.nonneg_iff.mp hC.posSemidef.det_nonneg).1
  have htrci : C.trace.im=0 := (Complex.nonneg_iff.mp hC.posSemidef.trace_nonneg).2.symm
  have htrcr : 0 ≤ C.trace.re := (Complex.nonneg_iff.mp hC.posSemidef.trace_nonneg).1
  have htrli : L.trace.im=0 := (Complex.nonneg_iff.mp hL.posSemidef.trace_nonneg).2.symm
  have htrpi : (L*C).trace.im=0 :=
    D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
      L C hL.isHermitian hC.isHermitian
  have hdetC : C.det=(d:ℂ) := by
    have he := congrArg Matrix.det hCL
    simp only [Matrix.det_mul,hdetL,mul_one,hdetW] at he
    have hre := congrArg Complex.re he
    simp only [Complex.mul_re,hci,mul_zero,sub_zero,Complex.ofReal_re] at hre
    have hsq : C.det.re^2=d^2 := by nlinarith only [hre]
    have hr := (sq_eq_sq₀ hcr hd.le).mp hsq
    exact Complex.ext hr (by simpa using hci)
  have htrace : W.trace.re+d*L.trace.re=(L*C).trace.re*C.trace.re := by
    have hs := D5.S0.Observation.MatrixTracePowerSum.pow_add_two C 0
    norm_num only [zero_add,pow_zero,pow_one] at hs
    have ht := congrArg (fun M : (Matrix (Fin 2) (Fin 2) ℂ) => (L*M).trace) hs
    have hw : (L*C^2).trace=W.trace := by
      rw [pow_two,← mul_assoc,Matrix.trace_mul_cycle,hCL]
    simp only [Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,
      smul_eq_mul,mul_one,hw,hdetC] at ht
    have hre := congrArg Complex.re ht
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      htrci,htrli,htrpi,mul_zero,zero_mul,sub_zero] at hre
    nlinarith only [hre]
  have htrace2 : (L*W).trace.re+2*d=(L*C).trace.re^2 := by
    have hs := D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two (L*C) 0
    have hw : (L*C)^2=L*W := by rw [pow_two,← hCL]; noncomm_ring
    norm_num only [zero_add,pow_zero,pow_one,Matrix.trace_one,Matrix.det_mul,hdetL,
      one_mul,hdetC,hw,Fintype.card_fin] at hs
    have hre := congrArg Complex.re hs
    norm_num only [Complex.sub_re,Complex.mul_re,htrpi,Complex.ofReal_re,
      Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,
      sub_zero] at hre
    nlinarith only [hre]
  exact ⟨hdetC, htrace, htrace2⟩

private theorem trace_obstruction {L W C : (Matrix (Fin 2) (Fin 2) ℂ)} {d : ℝ}
    (hL : L.PosDef) (hC : C.PosDef)
    (hd : 0 < d) (hdetL : L.det=1) (hdetW : W.det=(d^2:ℝ))
    (hCL : C*L*C=W)
    (hT : 0 < (W.trace.re+d*L.trace.re)^2-
      (1+d)^2*((L*W).trace.re+2*d)) : ¬ (1:(Matrix (Fin 2) (Fin 2) ℂ)) ≤ C := by
  obtain ⟨hdetC, htrace, htrace2⟩ :=
    transport_trace_identities hL hC hd hdetL hdetW hCL
  have htrcr : 0 ≤ C.trace.re := (Complex.nonneg_iff.mp hC.posSemidef.trace_nonneg).1
  intro hnear
  have hp : (C-1).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hnear)
  have hdif : (C-1).det=C.det-C.trace+1 := by
    simp only [Matrix.det_fin_two,Matrix.trace_fin_two,Matrix.sub_apply,Matrix.one_apply,
      Fin.isValue,ite_true,ite_false,sub_zero]
    norm_num <;> ring
  have hpd := (Complex.nonneg_iff.mp hp.det_nonneg).1
  rw [hdif,hdetC] at hpd
  simp only [Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.one_re] at hpd
  have hcb : C.trace.re≤1+d := by linarith
  have hsqb : C.trace.re^2≤(1+d)^2 :=
    (sq_le_sq₀ htrcr (by linarith : 0≤1+d)).2 hcb
  have hb := mul_le_mul_of_nonneg_left hsqb (sq_nonneg (L*C).trace.re)
  rw [htrace,htrace2] at hT
  nlinarith only [hT,hb]

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

private def witnessD : ℝ := 5/8+10/z

private theorem witnessD_pos : 0<witnessD := by
  have hz : 0<z := Real.sqrt_pos.mpr (by norm_num)
  unfold witnessD
  positivity

private theorem witnessL_det : witnessL.det=1 := by
  have hg : (g:ℂ)^2=15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤15))
  have hu : (rootU:ℂ)≠0 := by exact_mod_cast ne_of_gt (lt_trans (by norm_num) rootU_bounds.1)
  simp [witnessL,Matrix.det_fin_two,Complex.ofReal_div,Complex.ofReal_add,
    Complex.ofReal_sub,Complex.ofReal_mul]
  field_simp [hu]
  ring_nf
  simp only [hg]
  ring

private theorem witnessL_pos : witnessL.PosDef := by
  have hu : 0<rootU := lt_trans (by norm_num) rootU_bounds.1
  have hD : (diagonal ![(rootU:ℂ),((1/rootU:ℝ):ℂ)] : (Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · change (0:ℂ)<(rootU:ℂ)
      exact_mod_cast hu
    · change (0:ℂ)<((1/rootU:ℝ):ℂ)
      exact_mod_cast one_div_pos.mpr hu
  rw [witnessL_spectral]
  have hV : IsUnit eigenV := Unitary.isUnit_coe (U := (⟨eigenV,eigenV_unitary⟩ : Matrix.unitaryGroup (Fin 2) ℂ))
  simpa only [star_eq_conjTranspose] using hV.posDef_star_right_conjugate_iff.mpr hD

private theorem witnessW_affine : witnessW=(1/4:ℝ) •
    (witnessA+witnessB+witnessA*witnessK+witnessK*witnessA) := by
  unfold witnessW
  rw [← witnessK_riccati]
  congr 1
  noncomm_ring

private theorem witnessK_det : witnessK.det=(1/4:ℂ) := by
  have hg : (g:ℂ)^2=15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤15))
  have hzz : (z:ℂ)^2=265 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤265))
  have hz : (z:ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<265))
  simp [witnessK,Matrix.det_fin_two,Complex.ofReal_div,Complex.ofReal_mul]
  field_simp [hz]
  ring_nf
  simp only [hg,hzz]
  ring

private theorem witnessK_trace : witnessK.trace=((20/z:ℝ):ℂ) := by
  simp [witnessK,Matrix.trace_fin_two,Complex.ofReal_div,Complex.ofReal_mul]
  ring

private theorem witnessW_det : witnessW.det=((witnessD^2:ℝ):ℂ) := by
  have hdetI : (1+witnessK).det=(2:ℝ)*witnessD := by
    have hgen (M:(Matrix (Fin 2) (Fin 2) ℂ)) : (1+M).det=1+M.trace+M.det := by
      simp only [Matrix.det_fin_two,Matrix.trace_fin_two,Matrix.add_apply,
        Matrix.one_apply,Fin.isValue,ite_true,ite_false,zero_add]
      norm_num
      ring
    rw [hgen,witnessK_trace,witnessK_det]
    simp [witnessD,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_mul]
    ring
  unfold witnessW
  rw [Matrix.det_smul_of_tower,Matrix.det_mul,Matrix.det_mul,hdetI]
  norm_num [witnessA,Matrix.det_fin_two,Complex.real_smul,Complex.ofReal_pow]
  ring

private theorem witnessW_trace : witnessW.trace.re=25/16+265/(16*z) := by
  rw [witnessW_affine]
  norm_num [witnessA,witnessB,witnessK,Matrix.trace_fin_two,Matrix.mul_apply,
    Fin.sum_univ_two,Matrix.smul_apply,Complex.add_re,Complex.mul_re,Complex.smul_re,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.inv_re,Complex.normSq_ofReal]
  try ring_nf
  try simp only [← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero]
  norm_num
  ring

private theorem witnessL_trace : witnessL.trace.re=rootU+1/rootU := by
  norm_num [witnessL,Matrix.trace_fin_two]
  ring

private theorem witnessLW_trace : (witnessL*witnessW).trace.re=
    115*rootU/128+325*rootU/(32*z)+85/(128*rootU)+205/(32*rootU*z) := by
  have hg : g^2=15 := Real.sq_sqrt (by norm_num)
  have hu : rootU≠0 := ne_of_gt (lt_trans (by norm_num) rootU_bounds.1)
  have hz : z≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [witnessW_affine]
  norm_num [witnessL,witnessA,witnessB,witnessK,Matrix.trace_fin_two,Matrix.mul_apply,
    Fin.sum_univ_two,Matrix.smul_apply,Complex.add_re,Complex.mul_re,Complex.smul_re,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.inv_re,Complex.normSq_ofReal]
  try ring_nf
  try simp only [← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero]
  norm_num
  field_simp [hu,hz]
  ring_nf
  simp only [hg]
  ring

private theorem witness_trace_test : (3/2500:ℝ) <
    (witnessW.trace.re+witnessD*witnessL.trace.re)^2-
      (1+witnessD)^2*((witnessL*witnessW).trace.re+2*witnessD) := by
  rw [witnessW_trace,witnessL_trace,witnessLW_trace]
  exact trace_sign_by_intervals rootU_bounds.1 rootU_bounds.2 rootZ_bounds.1 rootZ_bounds.2

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open private geometric_inverse from D5.S3.Quantum.Matrix.GanKimConjectureRefutation
open D5.S3.Quantum.Hiai.PsiMeanTraceConcavity (geometricMean)

private theorem nearOrder_riccati {L W : Matrix (Fin 2) (Fin 2) ℂ}
    (hL : L.PosDef) (hW : W.PosDef) :
    (geometricMean (1/2) L⁻¹ W).PosDef ∧
    geometricMean (1/2) L⁻¹ W * L * geometricMean (1/2) L⁻¹ W = W := by
  rw [geometric_inverse hL hW]
  exact D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati hL hW
end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

private theorem wasserstein_witness :
    wassersteinBarycenter (fun _ : Fin 2 => (1/2:ℝ)) ![witnessA,witnessB] = witnessW := by
  rw [← witnessK_riccati, binary_midpoint_barycenter witnessA_pos witnessK_pos]
  unfold witnessW
  simp only [smul_mul_assoc,Matrix.mul_smul,smul_smul]
  norm_num

theorem result : ¬ claim := by
  intro hc
  have ha : ∀ j : Fin 2, (![witnessA,witnessB] j).PosDef := by
    intro j
    fin_cases j
    · exact witnessA_pos
    · exact witnessB_pos
  have hn := hc 2 (by norm_num) 2 (by norm_num) (fun _ => (1/2:ℝ))
    (by intro j; norm_num) (by norm_num [Fin.sum_univ_two]) ![witnessA,witnessB] ha
  rw [logEuclidean_witness,wasserstein_witness] at hn
  have hr := nearOrder_riccati witnessL_pos witnessW_pos
  exact trace_obstruction witnessL_pos hr.1 witnessD_pos witnessL_det
    witnessW_det hr.2 (lt_trans (by norm_num) witness_trace_test) hn

end D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
