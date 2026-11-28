/- GID: D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quadratic bound for the complementary effect in the Petz and Gibbs overlap. -/

import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Schatten.Holder
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Matrix.BlockEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The quadratic estimate for the second flag of the physical qutrit Petz example. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritSecondFlag

open scoped CStarAlgebra ComplexOrder _root_.Matrix MatrixOrder Matrix.Norms.L2Operator
open NormedSpace
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open RHLinalg (trace_mul_nonneg_of_posSemidef)

local notation "mat" => CStarMatrix.ofMatrix.symm

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ (CStarMatrix n n ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass'

private theorem schattenNorm_one_eq_traceNorm (A : Matrix n n ℂ) :
    schattenNorm A 1 = traceNorm A := by
  have hGram := Matrix.isHermitian_mul_conjTranspose_self Aᴴ
  unfold schattenNorm traceNorm
  simp only [div_one, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [← hGram.cfc_eq, Matrix.conjTranspose_conjTranspose,
    CFC.sqrt_eq_real_sqrt (Aᴴ * A) (Matrix.posSemidef_conjTranspose_mul_self A).nonneg,
    cfcₙ_eq_cfc]

private theorem schattenNorm_two_eq_sqrt_trace (A : Matrix n n ℂ) :
    schattenNorm A 2 = Real.sqrt (Aᴴ * A).trace.re := by
  have hGram := Matrix.isHermitian_mul_conjTranspose_self Aᴴ
  have hc : hGram.cfc (fun x : ℝ => x) = Aᴴ * (Aᴴ)ᴴ :=
    (hGram.cfc_eq _).symm.trans (cfc_id' ℝ _ hGram.isSelfAdjoint)
  unfold schattenNorm
  simp only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  rw [hc, Matrix.conjTranspose_conjTranspose, RCLike.re_eq_complex_re, Real.sqrt_eq_rpow]

theorem mat_log {X : CStarMatrix n n ℂ} (hX : IsSelfAdjoint X) :
    mat (CFC.log X) = CFC.log (mat X) := by
  let A : Matrix n n ℂ := mat X
  have hA : IsSelfAdjoint A := hX.map CStarMatrix.ofMatrixStarAlgEquiv.symm
  have hlog : CStarMatrix.ofMatrix (cfc Real.log A) = CFC.log X :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log A
      (A.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hA hX
  exact congrArg mat hlog.symm

private theorem log_complement_lower {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -(x + x ^ 2) ≤ Real.log (1 - x) := by
  have hnorm : ‖-(x : ℂ)‖ = x := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  have harg : (1 : ℂ) + -(x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    simp [sub_eq_add_neg]
  have h := Complex.norm_log_one_add_sub_self_le (z := -(x : ℂ))
    (by rw [hnorm]; linarith)
  rw [harg, ← Complex.ofReal_log (by linarith : 0 ≤ 1 - x), sub_neg_eq_add,
    ← Complex.ofReal_add, hnorm, Complex.norm_real, Real.norm_eq_abs] at h
  have hinv : (1 - x)⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (one_div_le (by linarith : 0 < 1 - x) (by norm_num : (0 : ℝ) < 2)).2
      (by linarith)
  have herr : x ^ 2 * (1 - x)⁻¹ / 2 ≤ x ^ 2 := by
    calc
      x ^ 2 * (1 - x)⁻¹ / 2 ≤ x ^ 2 * 2 / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (sq_nonneg x)) (by norm_num)
      _ = _ := by ring
  linarith only [(abs_le.mp (h.trans herr)).1]

variable [Nonempty n]

set_option backward.isDefEq.respectTransparency false in
private theorem cfc_log_complement_lower (X : CStarMatrix n n ℂ) (hX : 0 ≤ X)
    (hhalf : X ≤ algebraMap ℝ (CStarMatrix n n ℂ) (1 / 2)) :
    -(X + X ^ 2) ≤ CFC.log (1 - X) := by
  let D := (1 : CStarMatrix n n ℂ) - X
  have hD : IsSelfAdjoint D := (IsSelfAdjoint.one _).sub (IsSelfAdjoint.of_nonneg hX)
  have hDlo : algebraMap ℝ (CStarMatrix n n ℂ) (1 / 2) ≤ D := by
    have he : (1 : CStarMatrix n n ℂ) - algebraMap ℝ (CStarMatrix n n ℂ) (1 / 2) =
        algebraMap ℝ (CStarMatrix n n ℂ) (1 / 2) := by
      rw [← map_one (algebraMap ℝ (CStarMatrix n n ℂ)), ← map_sub]
      norm_num
    rw [← he]
    exact sub_le_sub_left hhalf 1
  have hDhi : D ≤ 1 := sub_le_self 1 hX
  have hlo := (algebraMap_le_iff_le_spectrum (r := (1 / 2 : ℝ)) hD).1 hDlo
  have hhi := (le_algebraMap_iff_spectrum_le (r := (1 : ℝ)) hD).1
    (by simpa only [map_one] using hDhi)
  have hc : ContinuousOn (fun t : ℝ => 1 - t) (spectrum ℝ D) :=
    (continuous_const.sub continuous_id).continuousOn
  have hlog : ContinuousOn Real.log (spectrum ℝ D) :=
    continuousOn_id.log (fun t ht => by
      change t ≠ 0
      linarith [hlo t ht])
  have h := (cfc_le_iff (fun t : ℝ => -((1 - t) + (1 - t) ^ 2)) Real.log D
      (hc.add (hc.pow 2)).neg hlog hD).2 (by
    intro t ht
    simpa only [sub_sub_cancel] using log_complement_lower
      (sub_nonneg.mpr (hhi t ht)) (by linarith [hlo t ht]))
  rw [cfc_neg _ D,
    cfc_add (a := D) (fun t : ℝ => 1 - t) (fun t => (1 - t) ^ 2) hc (hc.pow 2),
    cfc_pow (fun t : ℝ => 1 - t) 2 D hc hD, cfc_sub (fun _ : ℝ => 1) (fun t => t) D
      continuousOn_const continuousOn_id, cfc_const_one ℝ D hD, cfc_id' ℝ D hD] at h
  rw [show 1 - D = X by simp only [D, sub_sub_cancel]] at h
  unfold CFC.log
  exact h

omit [Nonempty n] in
private theorem faithful_entropy_nonneg (Q G : DensityState n)
    (hQ : (mat Q.1).PosDef) (hG : (mat G.1).PosDef) :
    0 ≤ quantumRelativeEntropy Q G := by
  have hsupport (v : n → ℂ) (hv : mat G.1 *ᵥ v = 0) : mat Q.1 *ᵥ v = 0 := by
    have hv0 : v = 0 := hG.mulVec_injective (by simpa using hv)
    simp [hv0]
  have h := Omega.Matrix.BlockEntropy.trace_log_klein (mat Q.1) (mat G.1)
    hQ.posSemidef hG.posSemidef (Q.2.2.trans G.2.2.symm) hsupport
  unfold quantumRelativeEntropy
  change 0 ≤ (mat Q.1 * (mat (CFC.log Q.1) - mat (CFC.log G.1))).trace.re
  rw [mat_log Q.2.1.isSelfAdjoint, mat_log G.2.1.isSelfAdjoint,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  exact h.1

/-- The second-flag Gibbs partition function is bounded below by the quadratic trace
polynomial whenever the scaled first effect lies between zero and half the identity. -/
private theorem second_flag_bound (Q : DensityState n) (hQ : (mat Q.1).PosDef)
    (ε : ℝ) (M : CStarMatrix n n ℂ) (hM : 0 ≤ ε • M)
    (hhalf : ε • M ≤ algebraMap ℝ (CStarMatrix n n ℂ) (1 / 2)) :
    1 - ε * (mat (Q.1 * M)).trace.re - ε ^ 2 * (mat (Q.1 * M ^ 2)).trace.re ≤
      partitionFunction (CFC.log Q.1 + CFC.log (1 - ε • M)) := by
  let X := ε • M
  let L := CFC.log (1 - X)
  let H := CFC.log Q.1 + L
  have hH : IsSelfAdjoint H :=
    (IsSelfAdjoint.log (a := Q.1)).add (IsSelfAdjoint.log (a := 1 - X))
  have hG := faithful_entropy_nonneg Q (gibbsState H hH) hQ (gibbs_state_posDef H hH)
  have hgibbs := gibbs_variational_identity H hH Q
  change Real.log (partitionFunction H) =
    (((mat (CFC.log Q.1) + mat L) * mat Q.1).trace).re -
      (mat Q.1 * mat (CFC.log Q.1)).trace.re +
      quantumRelativeEntropy Q (gibbsState H hH) at hgibbs
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re,
    Matrix.trace_mul_comm (mat (CFC.log Q.1)) (mat Q.1),
    Matrix.trace_mul_comm (mat L) (mat Q.1)] at hgibbs
  have hZ := Real.add_one_le_exp (Real.log (partitionFunction H))
  rw [Real.exp_log (partition_function_pos H hH)] at hZ
  have hpoly := cfc_log_complement_lower X hM hhalf
  have hdiff : (mat (L - -(X + X ^ 2))).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sub_nonneg.mpr hpoly))
  have htr := trace_mul_nonneg_of_posSemidef hQ.posSemidef hdiff
  change 0 ≤ (mat Q.1 * (mat L - -(mat X + mat X ^ 2))).trace.re at htr
  simp only [Matrix.mul_sub, mul_neg, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_neg, Matrix.trace_add, Complex.sub_re, Complex.neg_re, Complex.add_re] at htr
  have hXsq : (ε • mat M) ^ 2 = ε ^ 2 • (mat M) ^ 2 := by
    simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
  change 0 ≤ (mat Q.1 * mat L).trace.re -
    -((mat Q.1 * (ε • mat M)).trace.re +
      (mat Q.1 * (ε • mat M) ^ 2).trace.re) at htr
  rw [hXsq, mul_smul_comm, mul_smul_comm, Matrix.trace_smul, Matrix.trace_smul] at htr
  simp only [Complex.smul_re, smul_eq_mul] at htr
  change 0 ≤ (mat Q.1 * mat L).trace.re -
    -(ε * (mat (Q.1 * M)).trace.re + ε ^ 2 * (mat (Q.1 * M ^ 2)).trace.re) at htr
  change _ ≤ partitionFunction H
  linarith only [hgibbs, hG, hZ, htr]


/-- The second flag contributes at most half the quadratic error to the overlap
deficit. The two factors for Hilbert–Schmidt Hölder are `√Ω` and `√D * √Q`. -/
theorem second_flag_traceNorm_sub_le (Q : DensityState n) (hQ : (mat Q.1).PosDef)
    (ε : ℝ) (M : CStarMatrix n n ℂ) (hM : 0 ≤ ε • M)
    (hhalf : ε • M ≤ algebraMap ℝ (CStarMatrix n n ℂ) (1 / 2)) :
    let D := 1 - ε • M
    let H := CFC.log Q.1 + CFC.log D
    traceNorm (mat (CFC.sqrt (exp H) * CFC.sqrt D * CFC.sqrt Q.1)) -
      partitionFunction H ≤ ε ^ 2 * (mat (Q.1 * M ^ 2)).trace.re / 2 := by
  let D := 1 - ε • M
  let H := CFC.log Q.1 + CFC.log D
  let Ω := exp H
  let R := mat (CFC.sqrt Ω)
  let S := mat (CFC.sqrt D)
  let T := mat (CFC.sqrt Q.1)
  have hD : 0 ≤ D := sub_nonneg.mpr (hhalf.trans (by
    rw [← map_one (algebraMap ℝ (CStarMatrix n n ℂ))]
    exact algebraMap_mono (CStarMatrix n n ℂ) (by norm_num : (1 / 2 : ℝ) ≤ 1)))
  have hH : IsSelfAdjoint H :=
    (IsSelfAdjoint.log (a := Q.1)).add (IsSelfAdjoint.log (a := D))
  let : NormedAlgebra ℚ (CStarMatrix n n ℂ) := .restrictScalars ℚ ℂ _
  have hΩ : 0 ≤ Ω := hH.exp_nonneg
  have root_star (F : CStarMatrix n n ℂ) : (mat (CFC.sqrt F))ᴴ = mat (CFC.sqrt F) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg F)).star_eq
  have hRR : R * R = mat Ω := congrArg mat (CFC.sqrt_mul_sqrt_self Ω hΩ)
  have hSS : S * S = mat D := congrArg mat (CFC.sqrt_mul_sqrt_self D hD)
  have hTT : T * T = mat Q.1 := congrArg mat (CFC.sqrt_mul_sqrt_self Q.1 Q.2.1)
  have hR : (Rᴴ * R).trace.re = partitionFunction H := by
    change (Rᴴ * R).trace.re = (mat Ω).trace.re
    rw [show Rᴴ = R from root_star Ω, hRR]
  have hST : ((S * T)ᴴ * (S * T)).trace.re = (mat (Q.1 * D)).trace.re := by
    rw [Matrix.conjTranspose_mul, show Tᴴ = T from root_star Q.1,
      show Sᴴ = S from root_star D]
    calc
      ((T * S) * (S * T)).trace.re = (T * (S * S) * T).trace.re := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hSS, Matrix.trace_mul_cycle, hTT]
        rfl
  have hholder := schattenNorm_mul_le R (S * T) (r := 1) (p := 2) (q := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [schattenNorm_one_eq_traceNorm, schattenNorm_two_eq_sqrt_trace R,
    schattenNorm_two_eq_sqrt_trace (S * T), hR, hST, ← Matrix.mul_assoc] at hholder
  have hd : 0 ≤ (mat (Q.1 * D)).trace.re :=
    trace_mul_nonneg_of_posSemidef hQ.posSemidef
      (Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hD))
  have hmean : Real.sqrt (partitionFunction H) * Real.sqrt (mat (Q.1 * D)).trace.re ≤
      (partitionFunction H + (mat (Q.1 * D)).trace.re) / 2 := by
    nlinarith only [sq_nonneg (Real.sqrt (partitionFunction H) -
      Real.sqrt (mat (Q.1 * D)).trace.re),
      Real.sq_sqrt (partition_function_pos H hH).le, Real.sq_sqrt hd]
  have htrace : (mat (Q.1 * D)).trace.re = 1 - ε * (mat (Q.1 * M)).trace.re := by
    change (mat Q.1 * (1 - ε • mat M)).trace.re = _
    rw [Matrix.mul_sub, Matrix.mul_one, mul_smul_comm, Matrix.trace_sub, Matrix.trace_smul,
      show (mat Q.1).trace = 1 from Q.2.2]
    simp only [Complex.sub_re, Complex.one_re, Complex.smul_re, smul_eq_mul]
    rfl
  have hZ : _ ≤ partitionFunction H := second_flag_bound Q hQ ε M hM hhalf
  change traceNorm (R * S * T) - partitionFunction H ≤ _
  linarith only [hholder.trans hmean, htrace, hZ]

end D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritSecondFlag
