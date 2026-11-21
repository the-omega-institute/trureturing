/- GID: D5/S3/Quantum/Analysis/RefinedBMVLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite-dimensional three-by-three refined BMV exponential lower bound. -/

import D5.S3.Quantum.Analysis.RefinedBMV33
import D5.S3.Quantum.Analysis.RefinedBMVTracePower
import D5.S3.Quantum.Analysis.TrotterProduct
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

open Matrix NormedSpace Filter
open scoped CStarAlgebra MatrixOrder ComplexOrder Topology Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "CMat" => CStarMatrix (Fin n) (Fin n) ℂ

section NonemptyDimension

variable [NeZero n]

private theorem exp_posDef {H : Mat} (hH : H.IsHermitian) : (exp H).PosDef := by
  letI : NormedAlgebra ℚ CMat := NormedAlgebra.restrictScalars ℚ ℂ _
  let A : CMat := CStarMatrix.ofMatrix H
  have hA : IsSelfAdjoint A := by
    change star (CStarMatrix.ofMatrixStarAlgEquiv H) = CStarMatrix.ofMatrixStarAlgEquiv H
    rw [← map_star]
    exact congrArg CStarMatrix.ofMatrixStarAlgEquiv hH.star_eq
  have hbridge : CStarMatrix.ofMatrixStarAlgEquiv.symm (exp A) = exp H :=
    NormedSpace.map_exp CStarMatrix.ofMatrixStarAlgEquiv.symm
      CStarMatrix.ofMatrixL.symm.continuous A
  rw [← hbridge]
  have hn := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hA.exp_nonneg
  apply (Matrix.nonneg_iff_posSemidef.mp hn).posDef_iff_isUnit.mpr
  rw [hbridge]
  exact Matrix.isUnit_exp H

private theorem hermitian_real_smul {H : Mat} (hH : H.IsHermitian) (r : ℝ) :
    (r • H).IsHermitian := by
  change (r • H)ᴴ = r • H
  rw [conjTranspose_smul, hH.eq]
  simp

private noncomputable def dyadicTrace (H K : Mat) (j : ℕ) : ℝ :=
  (trace ((exp (((2 : ℝ) ^ j)⁻¹ • H) * exp (((2 : ℝ) ^ j)⁻¹ • K)) ^
    (3 * 2 ^ j))).re

private theorem dyadicTrace_step (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (j : ℕ) : dyadicTrace H K (j + 1) ≤ dyadicTrace H K j := by
  let s : ℝ := ((2 : ℝ) ^ (j + 1))⁻¹
  have hs : (2 : ℕ) • (s • H) = ((2 : ℝ) ^ j)⁻¹ • H := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    dsimp only [s]
    rw [pow_succ, _root_.mul_inv_rev]
    norm_num [← mul_assoc]
  have hs' : (2 : ℕ) • (s • K) = ((2 : ℝ) ^ j)⁻¹ • K := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    dsimp only [s]
    rw [pow_succ, _root_.mul_inv_rev]
    norm_num [← mul_assoc]
  have h := trace_mul_two_pow_le (exp (s • H)) (exp (s • K))
    (exp_posDef (hermitian_real_smul hH s)) (exp_posDef (hermitian_real_smul hK s))
    (3 * 2 ^ j)
  rw [← Matrix.exp_nsmul, ← Matrix.exp_nsmul, hs, hs'] at h
  have hp : 2 * (3 * 2 ^ j) = 3 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  rw [hp] at h
  exact h

private theorem dyadicTrace_tendsto (H K : Mat) :
    Tendsto (dyadicTrace H K) atTop (𝓝 (trace (exp ((3 : ℝ) • H + (3 : ℝ) • K))).re) := by
  letI : NormedAlgebra ℚ CMat := NormedAlgebra.restrictScalars ℚ ℂ _
  let f := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)
  let g := f.symm
  have hc : Continuous (fun A : CMat ↦ (trace (g A)).re) :=
    Complex.continuous_re.comp (CStarMatrix.ofMatrixL.symm.continuous.matrix_trace)
  have ht : Tendsto (fun j : ℕ ↦ 3 * 2 ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by decide)).const_mul_atTop'
      (show (0 : ℕ) < 3 by decide)
  have h := (NormedSpace.trotter_product ((3 : ℝ) • f H) ((3 : ℝ) • f K)).comp ht
  have h' := hc.continuousAt.tendsto.comp h
  have hExp (X : CMat) : g (exp X) = exp (g X) :=
    NormedSpace.map_exp g CStarMatrix.ofMatrixL.symm.continuous X
  have hgs (r : ℝ) (A : CMat) : g (r • A) = r • g A := rfl
  have hScalar (j : ℕ) : ((↑(3 * 2 ^ j : ℕ) : ℝ)⁻¹ * 3) = ((2 : ℝ) ^ j)⁻¹ := by
    push_cast
    rw [_root_.mul_inv_rev, mul_assoc]
    norm_num
  let step (j : ℕ) (M : Mat) : CMat := ((↑(3 * 2 ^ j : ℕ) : ℝ)⁻¹) • ((3 : ℝ) • f M)
  have hstep (j : ℕ) (M : Mat) : g (step j M) = ((2 : ℝ) ^ j)⁻¹ • M := by
    change ((↑(3 * 2 ^ j : ℕ) : ℝ)⁻¹) • ((3 : ℝ) • M) = _
    rw [smul_smul, hScalar]
  have hseq : (fun j : ℕ ↦ (trace (g ((exp (step j H) * exp (step j K)) ^
      (3 * 2 ^ j)))).re) = dyadicTrace H K := by
    funext j
    rw [map_pow g, map_mul g, hExp, hExp, hstep j H, hstep j K]
    rfl
  rw [← hseq]
  change Tendsto (fun j : ℕ ↦ (trace (g ((exp (step j H) * exp (step j K)) ^
      (3 * 2 ^ j)))).re) atTop (𝓝 (trace (g (exp ((3 : ℝ) • f H + (3 : ℝ) • f K)))).re) at h'
  simpa only [hExp, map_add, hgs, g, StarAlgEquiv.symm_apply_apply] using h'

/-- Dyadic trace-power comparison against the Trotter limit. -/
theorem exponential_trace_le_cube (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (trace (exp ((3 : ℝ) • H + (3 : ℝ) • K))).re ≤
      (trace ((exp H * exp K) ^ 3)).re := by
  have hmono : Antitone (dyadicTrace H K) :=
    antitone_nat_of_succ_le (dyadicTrace_step H K hH hK)
  have h := le_of_tendsto' (dyadicTrace_tendsto H K) (fun j ↦ hmono (Nat.zero_le j))
  simpa [dyadicTrace] using h

end NonemptyDimension

/-- For all finite-dimensional complex Hermitian inputs, the mean of the twenty words
with three copies of each exponential is at least the trace of `exp (3H + 3K)`. -/
theorem L33_all (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((3 : ℝ) • H + (3 : ℝ) • K)) ≤ wordMean (exp H) (exp K) := by
  by_cases hn : n = 0
  · subst n
    simp [wordMean, trace_eq_zero_of_isEmpty]
  letI : NeZero n := ⟨hn⟩
  have hE := E33_all _ _ (exp_posDef hH).posSemidef (exp_posDef hK).posSemidef
  refine Complex.le_def.mpr ⟨(exponential_trace_le_cube H K hH hK).trans
    (Complex.le_def.mp hE).1, ?_⟩
  have hh := ((hermitian_real_smul hH 3).add (hermitian_real_smul hK 3)).exp
  have ht : IsSelfAdjoint (trace (exp ((3 : ℝ) • H + (3 : ℝ) • K))) := by
    change star (trace _) = _
    rw [← trace_conjTranspose, hh.eq]
  rw [(Complex.im_eq_zero_iff_isSelfAdjoint _).mpr ht,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
      (wordMean_isSelfAdjoint (exp H) (exp K) hH.exp hK.exp)]

/-- The refined BMV exponential lower bound in dimension four. -/
theorem L33 (H K : Matrix (Fin 4) (Fin 4) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (trace (exp ((3 : ℝ) • H + (3 : ℝ) • K))).re ≤ (wordMean (exp H) (exp K)).re :=
  (Complex.le_def.mp (L33_all H K hH hK)).1

theorem L33_complex (H K : Matrix (Fin 4) (Fin 4) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((3 : ℝ) • H + (3 : ℝ) • K)) ≤ wordMean (exp H) (exp K) :=
  L33_all H K hH hK

#print axioms exponential_trace_le_cube
#print axioms L33_all
#print axioms L33
#print axioms L33_complex

end RefinedBMV
