/- GID: D5/S3/Quantum/Hiai/ForwardTraceYoung
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/ForwardTraceYoung
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forward tracial Young inequality and its positive definite maximizing optimizer. -/

import D5.S3.Quantum.Hiai.InverseMeanVariational
import Mathlib.Analysis.MeanInequalities

noncomputable section
namespace D5.S3.Quantum.Hiai.ForwardTraceYoung
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix D5.S3.Quantum.Hiai.InverseMeanVariational
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- The maximized forward trace-Young objective. -/
def objective (p : ℝ) (M W : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (M * W ^ (1 - p))).re - (1 - p) * (Matrix.trace W).re

private lemma holder_trace {M W : Matrix d d ℂ} (hM : M.PosDef) (hW : W.PosDef)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (Matrix.trace (M * W ^ (1 - p))).re ≤
      tracePower (1 / p) M ^ p * (Matrix.trace W).re ^ (1 - p) ∧
    0 ≤ tracePower (1 / p) M ∧ 0 ≤ (Matrix.trace W).re := by
  let U := M ^ (1 / 2 : ℝ)
  let V := W ^ ((1 - p) / 2)
  let a := 2 / p
  let b := 2 / (1 - p)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hU : Uᴴ = U := (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := M))).star_eq
  have hV : Vᴴ = V := (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := W))).star_eq
  have hUU : U * U = M := by
    dsimp [U]
    rw [← CFC.rpow_add hM.isUnit]
    norm_num
    exact CFC.rpow_one M hM.posSemidef.nonneg
  have hVV : V * V = W ^ (1 - p) := by
    dsimp [V]
    rw [← CFC.rpow_add hW.isUnit]
    congr 1
    ring
  have hUV : schattenNorm (U * V) 2 ^ (2 : ℝ) =
      (Matrix.trace (M * W ^ (1 - p))).re := by
    rw [norm_rpow_gram _ (by norm_num)]
    norm_num only [tracePower, show (2 : ℝ) / 2 = 1 by norm_num]
    rw [CFC.rpow_one _ (Matrix.posSemidef_conjTranspose_mul_self (U * V)).nonneg,
      Matrix.conjTranspose_mul, hU, hV]
    have hg : V * U * (U * V) = V * M * V := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc V U U, hUU]
    rw [hg, Matrix.trace_mul_cycle, Matrix.trace_mul_comm (V * V) M, hVV]
  have hnormU : schattenNorm U a ^ a = tracePower (1 / p) M := by
    rw [norm_rpow_gram _ ha, hU, hUU]
    congr 1
    dsimp [a]
    ring
  have hnormV : schattenNorm V b ^ b = (Matrix.trace W).re := by
    rw [norm_rpow_gram _ hb, hV, hVV]
    dsimp [tracePower]
    rw [CFC.rpow_rpow W (1 - p) (b / 2) (by linarith) hW.isStrictlyPositive]
    have he : (1 - p) * (b / 2) = 1 := by dsimp [b]; field_simp [show 1 - p ≠ 0 by linarith]
    rw [he, CFC.rpow_one W hW.posSemidef.nonneg]
  have hTM : 0 ≤ tracePower (1 / p) M := by
    rw [← hnormU]
    exact Real.rpow_nonneg (schattenNorm_nonneg U _) _
  have hTW : 0 ≤ (Matrix.trace W).re := by
    rw [← hnormV]
    exact Real.rpow_nonneg (schattenNorm_nonneg V _) _
  have hh := schattenNorm_mul_le U V (by norm_num : (0 : ℝ) < 2) ha hb
    (by dsimp [a, b]; field_simp; ring : 1 / (2 : ℝ) = 1 / a + 1 / b)
  have hh2 := Real.rpow_le_rpow (schattenNorm_nonneg (U * V) _) hh (by norm_num : (0 : ℝ) ≤ 2)
  rw [hUV, Real.mul_rpow (schattenNorm_nonneg U _) (schattenNorm_nonneg V _)] at hh2
  have heU : schattenNorm U  a ^ (2 : ℝ) = tracePower (1 / p) M ^ p := by
    rw [← hnormU, ← Real.rpow_mul (schattenNorm_nonneg U _)]
    have he : a * p = 2 := by dsimp [a]; field_simp
    rw [he]
  have heV : schattenNorm V b ^ (2 : ℝ) = (Matrix.trace W).re ^ (1 - p) := by
    rw [← hnormV, ← Real.rpow_mul (schattenNorm_nonneg V _)]
    have he : b * (1 - p) = 2 := by dsimp [b]; field_simp [show 1 - p ≠ 0 by linarith]
    rw [he]
  exact ⟨by simpa only [heU, heV] using hh2, hTM, hTW⟩

/-- Universal forward Young bound for arbitrary noncommuting positive definite matrices. -/
theorem forward_trace_young {M W : Matrix d d ℂ} (hM : M.PosDef) (hW : W.PosDef)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    objective p M W ≤ p * tracePower (1 / p) M := by
  by_cases h1 : p = 1
  · subst p
    simp [objective, tracePower, CFC.rpow_one M hM.posSemidef.nonneg,
      CFC.rpow_zero W hW.posSemidef.nonneg]
  · have hp1' : p < 1 := lt_of_le_of_ne hp1 h1
    obtain ⟨hh, hTM, hTW⟩ := holder_trace hM hW hp hp1'
    have hy := Real.geom_mean_le_arith_mean2_weighted hp.le (sub_nonneg.mpr hp1)
      hTM hTW (by ring : p + (1 - p) = 1)
    unfold objective
    linarith

/-- The strictly positive optimizer is exactly `M^(1/p)`, including the endpoint `p=1`. -/
theorem maximum_and_attainment {M : Matrix d d ℂ} (hM : M.PosDef)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ W₀ : Matrix d d ℂ, W₀.PosDef ∧ W₀ = M ^ (1 / p) ∧
      objective p M W₀ = p * tracePower (1 / p) M ∧
      ∀ W : Matrix d d ℂ, W.PosDef → objective p M W ≤ objective p M W₀ := by
  have hW₀ : (M ^ (1 / p)).PosDef := (hM.isStrictlyPositive.rpow M (1 / p)).posDef
  have heq : objective p M (M ^ (1 / p)) = p * tracePower (1 / p) M := by
    have hprod : M * ((M ^ (1 / p)) ^ (1 - p)) = M ^ (1 / p) := by
      rw [CFC.rpow_rpow M (1 / p) (1 - p) (by positivity) hM.isStrictlyPositive]
      conv_lhs => lhs; rw [← CFC.rpow_one M hM.posSemidef.nonneg]
      rw [← CFC.rpow_add hM.isUnit]
      congr 1
      field_simp
      ring
    rw [objective, hprod, tracePower]
    ring
  exact ⟨_, hW₀, rfl, heq, fun W hW ↦ heq.symm ▸ forward_trace_young hM hW hp hp1⟩

#print axioms forward_trace_young
#print axioms maximum_and_attainment
end D5.S3.Quantum.Hiai.ForwardTraceYoung
