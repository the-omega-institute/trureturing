/- GID: D5/S3/Analytic/Variational/JointReciprocalFunctional
   generality: G
   mirror-B: D5/B/S3/Analytic/Variational/JointReciprocalFunctional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructive scalar coordinates for the joint reciprocal integral functional. -/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

/-! # The joint reciprocal functional and its scalar coordinate -/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace D5.S3.Analytic.Variational.JointReciprocalFunctional

/-- The quadratic denominator in the scalar coordinate. -/
def polynomial (b v : ℝ) : ℝ := 2 * b + 3 * (1 - b) * v - 6 * v ^ 2

/-- The positive zero of the scalar denominator. -/
def upperRoot (b : ℝ) : ℝ :=
  (3 * (1 - b) + Real.sqrt (9 * (1 - b) ^ 2 + 48 * b)) / 12

/-- The magnitude of its negative zero. -/
def lowerRoot (b : ℝ) : ℝ :=
  (Real.sqrt (9 * (1 - b) ^ 2 + 48 * b) - 3 * (1 - b)) / 12

private def radius (b : ℝ) : ℝ := min (lowerRoot b / 2) (b / 6)
private def coordinateDomain (b : ℝ) : Set ℝ := Ioo (-radius b) (upperRoot b)

/-- The original oriented scalar integral, including a neighborhood of zero. -/
def coordinate (b v : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..v, (2 * b + 6 * s) / polynomial b s

/-- The mass and cumulative mass of a competitor on the original interval. -/
def mass (u : ℝ → ℝ) : ℝ := ∫ x in (1 : ℝ)..2, u x

def primitive (u : ℝ → ℝ) (x : ℝ) : ℝ := ∫ s in (1 : ℝ)..x, u s

/-- Both terms of the original functional; no competitor smoothness is imposed. -/
def cost (b : ℝ) (u : ℝ → ℝ) : ℝ :=
  b * (∫ x in (1 : ℝ)..2, x / u x) +
    ∫ x in (1 : ℝ)..2, primitive u x / (u x) ^ 2

/-- The full bounded positive measurable competitor class, with individual bounds. -/
def Admissible (u : ℝ → ℝ) : Prop :=
  Measurable u ∧ ∃ c B : ℝ, 0 < c ∧
    ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), c ≤ u x ∧ u x ≤ B

private lemma roots (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 < upperRoot b ∧ 0 < lowerRoot b ∧
      upperRoot b - lowerRoot b = (1 - b) / 2 ∧
      upperRoot b * lowerRoot b = b / 3 := by
  have hd : 0 ≤ 9 * (1 - b) ^ 2 + 48 * b := by positivity
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg (9 * (1 - b) ^ 2 + 48 * b)
  have hbig : 3 * (1 - b) < Real.sqrt (9 * (1 - b) ^ 2 + 48 * b) := by
    nlinarith [sq_nonneg (Real.sqrt (9 * (1 - b) ^ 2 + 48 * b) - 3 * (1 - b))]
  dsimp [upperRoot, lowerRoot]
  refine ⟨by positivity, by linarith, by ring, ?_⟩
  nlinarith

private lemma factorization (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (v : ℝ) :
    polynomial b v = 6 * (upperRoot b - v) * (v + lowerRoot b) := by
  obtain ⟨_, _, hd, hp⟩ := roots b hb hb1
  dsimp [polynomial]
  linear_combination -6 * v * hd - 6 * hp

private lemma radius_pos (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) : 0 < radius b := by
  exact lt_min (by linarith [(roots b hb hb1).2.1]) (by positivity)

private lemma domain_zero (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 ∈ coordinateDomain b :=
  ⟨neg_neg_of_pos (radius_pos b hb hb1), (roots b hb hb1).1⟩

private lemma domain_positive (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    0 < polynomial b v ∧ 0 < 2 * b + 6 * v ∧ 0 < v + lowerRoot b := by
  have hrad1 : radius b ≤ lowerRoot b / 2 := min_le_left _ _
  have hrad2 : radius b ≤ b / 6 := min_le_right _ _
  have hmu := (roots b hb hb1).2.1
  have hvm : 0 < v + lowerRoot b := by dsimp [coordinateDomain] at hv; linarith [hv.1]
  refine ⟨?_, ?_, hvm⟩
  · rw [factorization b hb hb1]
    exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hv.2)) hvm
  · dsimp [coordinateDomain] at hv
    linarith [hv.1]

private lemma integrand_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    ContDiffAt ℝ ∞ (fun s => (2 * b + 6 * s) / polynomial b s) v := by
  apply ContDiffAt.div
  · fun_prop
  · dsimp [polynomial]; fun_prop
  · exact ne_of_gt (domain_positive b hb hb1 hv).1

private lemma coordinate_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    HasDerivAt (coordinate b) ((2 * b + 6 * v) / polynomial b v) v := by
  have hz := domain_zero b hb hb1
  have hsub : uIcc 0 v ⊆ coordinateDomain b :=
    ordConnected_Ioo.uIcc_subset hz hv
  have hc : ContinuousOn (fun s => (2 * b + 6 * s) / polynomial b s) (uIcc 0 v) :=
    fun s hs => (integrand_contDiff b hb hb1 (hsub hs)).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable)
    ((fun s hs => (integrand_contDiff b hb hb1 hs).continuousAt).stronglyMeasurableAtFilter
      (isOpen_Ioo.mem_nhds hv)) (integrand_contDiff b hb hb1 hv).continuousAt

private lemma coordinate_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) : ContDiffAt ℝ ∞ (coordinate b) v := by
  have hi : ContDiffOn ℝ ∞ (fun s => (2 * b + 6 * s) / polynomial b s)
      (coordinateDomain b) := fun s hs => (integrand_contDiff b hb hb1 hs).contDiffWithinAt
  have hp : ContDiffOn ℝ ∞ (coordinate b) (coordinateDomain b) := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).2
    refine ⟨fun s hs => (coordinate_hasDerivAt b hb hb1 hs).differentiableAt.differentiableWithinAt, ?_⟩
    apply hi.congr
    intro s hs
    exact (coordinate_hasDerivAt b hb hb1 hs).deriv.symm
  exact hp.contDiffAt (isOpen_Ioo.mem_nhds hv)

private lemma coordinate_strictMono (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    StrictMonoOn (coordinate b) (coordinateDomain b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · exact fun v hv => (coordinate_hasDerivAt b hb hb1 hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [(coordinate_hasDerivAt b hb hb1 (interior_subset hv)).deriv]
    exact div_pos (domain_positive b hb hb1 (interior_subset hv)).2.1
      (domain_positive b hb hb1 (interior_subset hv)).1

end D5.S3.Analytic.Variational.JointReciprocalFunctional
