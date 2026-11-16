/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual signed external frequency vectors with their input-zero boundary. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose

/-! Frequency multiplication is realized by a finite difference of the original columns. -/

noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianAllIndexResolvent
open OriginalGaussianExternalResolvent OriginalGaussianDifferentiation
open OriginalGaussianBilinearTranspose
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

def externalParameter (out : Bool) (p : ℕ) : ℂ :=
  if out then (p : ℂ) + 1 / 2 else -(p : ℂ) - 1 / 2

def predecessor (out : Bool) (p : ℕ) : Bool × ℕ :=
  if out then (if p = 0 then (false, 0) else (true, p - 1)) else (false, p + 1)

private lemma predecessor_parameter (out : Bool) (p : ℕ) :
    externalParameter (predecessor out p).1 (predecessor out p).2 =
      externalParameter out p - 1 := by
  cases out
  · simp [predecessor, externalParameter]; ring
  · cases p with
    | zero => norm_num [predecessor, externalParameter]
    | succ p => simp [predecessor, externalParameter]; ring

private lemma choose_frequency (a : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * Ring.choose a (n + 1) =
      a * (Ring.choose a (n + 1) - Ring.choose (a - 1) (n + 1)) := by
  have h := Ring.choose_smul_choose a (n := n + 1) (k := 1) (by omega)
  have hp := Ring.choose_succ_succ (a - 1) n
  simp only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    Ring.choose_one_right, Nat.add_sub_cancel] at h
  rw [sub_add_cancel] at hp
  linear_combination h - a * hp

/-- This finite combination is an actual Hilbert-space vector. -/
def frequencyVector (out : Bool) (p : ℕ) (z : ℂ) : H :=
  externalParameter out p • (externalVector out p z -
    externalVector (predecessor out p).1 (predecessor out p).2 z)

lemma binomial_frequency (out : Bool) (p s : ℕ) :
    (s : ℂ) * externalBinomial out p s = externalParameter out p *
      (externalBinomial out p s -
        externalBinomial (predecessor out p).1 (predecessor out p).2 s) := by
  cases s with
  | zero => simp [externalBinomial]
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one]
    change (n + 1 : ℂ) * Ring.choose (externalParameter out p) (n + 1) =
      externalParameter out p * (Ring.choose (externalParameter out p) (n + 1) -
        Ring.choose (externalParameter (predecessor out p).1 (predecessor out p).2) (n + 1))
    rw [predecessor_parameter]
    exact choose_frequency (externalParameter out p) n

theorem frequencyVector_apply (out : Bool) (p : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) (n : ℕ) :
    frequencyVector out p z n = (n + 1 : ℂ) * externalColumn out p z n := by
  change externalParameter out p *
    (externalVector out p z n -
      externalVector (predecessor out p).1 (predecessor out p).2 z n) = _
  rw [externalVector_apply out p hz,
    externalVector_apply (predecessor out p).1 (predecessor out p).2 hz]
  simp only [externalColumn, externalBinomial]
  change externalParameter out p *
    (-(Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1) *
      Ring.choose (externalParameter out p) (n + 1) -
    -(Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1) *
      Ring.choose (externalParameter (predecessor out p).1
        (predecessor out p).2) (n + 1)) = _
  rw [predecessor_parameter]
  have h := choose_frequency (externalParameter out p) n
  change _ = (n + 1 : ℂ) * (-(Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1) *
    Ring.choose (externalParameter out p) (n + 1))
  linear_combination (Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1) * h

/-- The negative zero mode is exactly minus the weighted original source. -/
theorem externalVector_negative_zero {z : ℂ} (hz : ‖z‖ < 1) :
    externalVector false 0 z = -sourceFamily 1 z := by
  ext n
  change externalVector false 0 z n = -(sourceFamily 1 z n)
  rw [externalVector_apply false 0 hz, sourceFamily_apply 1 hz]
  simp only [externalColumn, externalBinomial, Bool.false_eq_true, ite_false,
    Nat.cast_zero, neg_zero, zero_sub, halfBinomial_choose, pow_one]
  have hs : (Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 = (n + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  have hn : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  field_simp [hn]
  rw [← hs]
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency
