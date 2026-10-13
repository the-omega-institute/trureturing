/- GID: D5/S3/Quantum/Hiai/ReverseTraceYoung
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/ReverseTraceYoung
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reverse trace Young with an attained positive definite minimum. -/

import D5.S3.Quantum.Hiai.InverseMeanVariational
import Mathlib.Analysis.MeanInequalities

/- The classical tracial Young variational formula is used in the Carlen-Lieb
   method, arXiv:0710.4167, and Zhang's variational method. The proof here
   consumes the attributed general Schatten Holder supplier. No originality
   is claimed for the inequality or its variational interpretation. -/

noncomputable section
namespace D5.S3.Quantum.Hiai.ReverseTraceYoung
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix InverseMeanVariational
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- The product inside the trace is not required to be selfadjoint. -/
def objective (a : ℝ) (M W : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (M * (W ^ (1 - a)))).re + (a - 1) * (Matrix.trace W).re

private lemma half_square {M : Matrix d d ℂ} (hM : M.PosDef) :
    (M ^ (1 / 2 : ℝ)) * (M ^ (1 / 2 : ℝ)) = M := by
  rw [← CFC.rpow_add hM.isUnit]
  norm_num
  exact CFC.rpow_one M hM.posSemidef.nonneg

private lemma holder_trace {M W : Matrix d d ℂ} (hM : M.PosDef) (hW : W.PosDef)
    {a : ℝ} (ha : 1 < a) :
    tracePower (1 / a) M ≤
      (Matrix.trace (M * (W ^ (1 - a)))).re ^ (1 / a) *
        (Matrix.trace W).re ^ ((a - 1) / a) ∧
      0 ≤ (Matrix.trace (M * (W ^ (1 - a)))).re ∧ 0 ≤ (Matrix.trace W).re := by
  have ha0 : 0 < a := by linarith
  have ham : 0 < a - 1 := by linarith
  let H := M ^ (1 / 2 : ℝ)
  let J := W ^ ((1 - a) / 2)
  let U := H * J
  let V := W ^ ((a - 1) / 2)
  let r := 2 / a
  let q := 2 / (a - 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hH : Hᴴ = H := (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := M))).star_eq
  have hJ : Jᴴ = J := (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := W))).star_eq
  have hV : Vᴴ = V := (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := W))).star_eq
  have hJJ : J * J = W ^ (1 - a) := by
    dsimp [J]
    rw [← CFC.rpow_add hW.isUnit]
    congr 1
    ring
  have hUV : U * V = H := by
    dsimp [U, V, J]
    rw [mul_assoc, ← CFC.rpow_add hW.isUnit]
    rw [show (1 - a) / 2 + (a - 1) / 2 = 0 by ring,
      CFC.rpow_zero W hW.posSemidef.nonneg, mul_one]
  have hnormH : schattenNorm (U * V) r ^ r = tracePower (1 / a) M := by
    rw [hUV, norm_rpow_gram _ hr, hH, half_square hM]
    congr 1
    dsimp [r]
    ring
  have hnormU : schattenNorm U 2 ^ (2 : ℝ) =
      (Matrix.trace (M * (W ^ (1 - a)))).re := by
    rw [norm_rpow_gram U (by norm_num)]
    have hgram : Uᴴ * U = J * M * J := by
      simp only [U, Matrix.conjTranspose_mul, hH, hJ, mul_assoc]
      rw [← mul_assoc H H J, half_square hM]
    norm_num only [tracePower, show (2 : ℝ) / 2 = 1 by norm_num]
    rw [CFC.rpow_one _ (Matrix.posSemidef_conjTranspose_mul_self U).nonneg, hgram]
    rw [Matrix.trace_mul_cycle, hJJ, Matrix.trace_mul_comm]
  have hnormV : schattenNorm V q ^ q = (Matrix.trace W).re := by
    rw [norm_rpow_gram V hq, hV]
    dsimp [V, tracePower]
    rw [← CFC.rpow_add hW.isUnit]
    rw [show (a - 1) / 2 + (a - 1) / 2 = a - 1 by ring,
      CFC.rpow_rpow W (a - 1) (q / 2) ham.ne' hW.isStrictlyPositive]
    rw [show (a - 1) * (q / 2) = 1 by dsimp [q]; field_simp,
      CFC.rpow_one W hW.posSemidef.nonneg]
  have hQ : 0 ≤ (Matrix.trace (M * (W ^ (1 - a)))).re := by
    rw [← hnormU]
    exact Real.rpow_nonneg (schattenNorm_nonneg U _) _
  have hS : 0 ≤ (Matrix.trace W).re := by
    rw [← hnormV]
    exact Real.rpow_nonneg (schattenNorm_nonneg V _) _
  refine ⟨?_, hQ, hS⟩
  have hh := schattenNorm_mul_le U V hr (by norm_num : 0 < (2 : ℝ)) hq
    (by dsimp [r, q]; field_simp; ring : 1 / r = 1 / 2 + 1 / q)
  have hh' := Real.rpow_le_rpow (schattenNorm_nonneg (U * V) _) hh hr.le
  rw [hnormH, Real.mul_rpow (schattenNorm_nonneg U _) (schattenNorm_nonneg V _)] at hh'
  have hUp : schattenNorm U 2 ^ r =
      (Matrix.trace (M * (W ^ (1 - a)))).re ^ (1 / a) := by
    rw [← hnormU, ← Real.rpow_mul (schattenNorm_nonneg U _)]
    congr 1
    dsimp [r]
    ring
  have hVp : schattenNorm V q ^ r = (Matrix.trace W).re ^ ((a - 1) / a) := by
    rw [← hnormV, ← Real.rpow_mul (schattenNorm_nonneg V _)]
    congr 1
    dsimp [r, q]
    field_simp
  rwa [hUp, hVp] at hh'

/-- Reverse trace Young for all a ≥ 1 and all finite dimensions, without commutation. -/
theorem reverse_trace_young {M W : Matrix d d ℂ} (hM : M.PosDef) (hW : W.PosDef)
    {a : ℝ} (ha : 1 ≤ a) : a * tracePower (1 / a) M ≤ objective a M W := by
  rcases eq_or_lt_of_le ha with ha | ha
  · rw [← ha]
    simp [objective, tracePower, CFC.rpow_one M hM.posSemidef.nonneg,
      CFC.rpow_zero W hW.posSemidef.nonneg]
  · have ha0 : 0 < a := by linarith
    obtain ⟨hh, hQ, hS⟩ := holder_trace hM hW ha
    have hw : 1 / a + (a - 1) / a = 1 := by field_simp; ring
    have hg := Real.geom_mean_le_arith_mean2_weighted
      (by positivity : 0 ≤ 1 / a) (by positivity : 0 ≤ (a - 1) / a) hQ hS hw
    calc
      a * tracePower (1 / a) M ≤
          a * ((1 / a) * (Matrix.trace (M * (W ^ (1 - a)))).re +
            ((a - 1) / a) * (Matrix.trace W).re) :=
        mul_le_mul_of_nonneg_left (hh.trans hg) ha0.le
      _ = objective a M W := by unfold objective; field_simp

/-- The positive definite optimizer M^(1/a) attains the unconditional global minimum.
No attainment over the positive definite cone is asserted for singular M. -/
theorem minimum_and_attainment {M : Matrix d d ℂ} (hM : M.PosDef)
    {a : ℝ} (ha : 1 ≤ a) :
    ∃ W₀ : Matrix d d ℂ, W₀.PosDef ∧ W₀ = M ^ (1 / a) ∧
      objective a M W₀ = a * tracePower (1 / a) M ∧
      ∀ W : Matrix d d ℂ, W.PosDef → objective a M W₀ ≤ objective a M W := by
  have ha0 : 0 < a := by linarith
  have hW : (M ^ (1 / a)).PosDef := (hM.isStrictlyPositive.rpow M (1 / a)).posDef
  have heq : objective a M (M ^ (1 / a)) = a * tracePower (1 / a) M := by
    have hprod : M * ((M ^ (1 / a)) ^ (1 - a)) = M ^ (1 / a) := by
      rw [CFC.rpow_rpow M (1 / a) (1 - a) (by positivity) hM.isStrictlyPositive]
      conv_lhs => lhs; rw [← CFC.rpow_one M hM.posSemidef.nonneg]
      rw [← CFC.rpow_add hM.isUnit]
      congr 1
      field_simp
      ring
    rw [objective, hprod, tracePower]
    ring
  refine ⟨M ^ (1 / a), hW, rfl, heq, ?_⟩
  intro W hW'
  rw [heq]
  exact reverse_trace_young hM hW' ha

#print axioms reverse_trace_young
#print axioms minimum_and_attainment
end D5.S3.Quantum.Hiai.ReverseTraceYoung
