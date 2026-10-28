/- GID: D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate
   generality: G
   mirror-B: D5/B/S3/Analytic/Variational/JointReciprocalScalarCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar integral coordinates, monotonicity and endpoint surjectivity for the joint reciprocal functional. -/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic

/-! # Scalar coordinate theory for the joint reciprocal functional -/

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

def radius (b : ℝ) : ℝ := min (lowerRoot b / 2) (b / 6)
def coordinateDomain (b : ℝ) : Set ℝ := Ioo (-radius b) (upperRoot b)

/-- The original oriented scalar integral, including a neighborhood of zero. -/
def coordinate (b v : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..v, (2 * b + 6 * s) / polynomial b s

lemma roots (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
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

lemma radius_pos (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) : 0 < radius b := by
  exact lt_min (by linarith [(roots b hb hb1).2.1]) (by positivity)

lemma domain_zero (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 ∈ coordinateDomain b :=
  ⟨neg_neg_of_pos (radius_pos b hb hb1), (roots b hb hb1).1⟩

lemma domain_positive (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
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
  · change ContDiffAt ℝ ∞ (fun s : ℝ => 2 * b + 3 * (1 - b) * s - 6 * s ^ 2) v
    fun_prop
  · exact ne_of_gt (domain_positive b hb hb1 hv).1

lemma coordinate_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    HasDerivAt (coordinate b) ((2 * b + 6 * v) / polynomial b v) v := by
  have hz := domain_zero b hb hb1
  have hsub : uIcc 0 v ⊆ coordinateDomain b :=
    ordConnected_Ioo.uIcc_subset hz hv
  have hc : ContinuousOn (fun s => (2 * b + 6 * s) / polynomial b s) (uIcc 0 v) :=
    fun s hs => (integrand_contDiff b hb hb1 (hsub hs)).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun s hs => (integrand_contDiff b hb hb1 hs).continuousAt) v hv) (integrand_contDiff b hb hb1 hv).continuousAt

lemma coordinate_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) : ContDiffAt ℝ ∞ (coordinate b) v := by
  have hi : ContDiffOn ℝ ∞ (fun s => (2 * b + 6 * s) / polynomial b s)
      (coordinateDomain b) := fun s hs => (integrand_contDiff b hb hb1 hs).contDiffWithinAt
  have hp : ContDiffOn ℝ ∞ (coordinate b) (coordinateDomain b) := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).2
    refine ⟨fun s hs => (coordinate_hasDerivAt b hb hb1 hs).differentiableAt.differentiableWithinAt, ?_⟩
    apply hi.congr
    intro s hs
    exact (coordinate_hasDerivAt b hb hb1 hs).deriv
  exact hp.contDiffAt (isOpen_Ioo.mem_nhds hv)

lemma coordinate_strictMono (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    StrictMonoOn (coordinate b) (coordinateDomain b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · exact fun v hv => (coordinate_hasDerivAt b hb hb1 hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [(coordinate_hasDerivAt b hb hb1 (interior_subset hv)).deriv]
    exact div_pos (domain_positive b hb hb1 (interior_subset hv)).2.1
      (domain_positive b hb hb1 (interior_subset hv)).1

private def logCoefficient (b : ℝ) : ℝ :=
  (upperRoot b + b / 3) / (upperRoot b + lowerRoot b)

private def logCoordinate (b v : ℝ) : ℝ :=
  logCoefficient b * (Real.log (upperRoot b) - Real.log (upperRoot b - v)) +
  (logCoefficient b - 1) * (Real.log (v + lowerRoot b) - Real.log (lowerRoot b))

private lemma logCoefficient_pos (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 < logCoefficient b := by
  obtain ⟨hn, hm, _, _⟩ := roots b hb hb1
  exact div_pos (by positivity) (add_pos hn hm)

private lemma logCoordinate_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    HasDerivAt (logCoordinate b) ((2 * b + 6 * v) / polynomial b v) v := by
  have hn : upperRoot b - v ≠ 0 := ne_of_gt (sub_pos.mpr hv.2)
  have hm : v + lowerRoot b ≠ 0 := ne_of_gt (domain_positive b hb hb1 hv).2.2
  have hsum : upperRoot b + lowerRoot b ≠ 0 :=
    ne_of_gt (add_pos (roots b hb hb1).1 (roots b hb hb1).2.1)
  have h := (((hasDerivAt_const v (Real.log (upperRoot b))).sub
    (((hasDerivAt_const v (upperRoot b)).sub (hasDerivAt_id v)).log hn)).const_mul
      (logCoefficient b)).add
    ((((hasDerivAt_id v).add_const (lowerRoot b)).log hm).sub_const
      (Real.log (lowerRoot b)) |>.const_mul (logCoefficient b - 1))
  convert h using 1
  · rfl
  · rw [factorization b hb hb1]
    dsimp [logCoefficient]
    field_simp
    <;> ring

private lemma coordinate_eq_logCoordinate (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) : coordinate b v = logCoordinate b v := by
  have hsub : uIcc 0 v ⊆ coordinateDomain b :=
    ordConnected_Ioo.uIcc_subset (domain_zero b hb hb1) hv
  have hi : IntervalIntegrable (fun s => (2 * b + 6 * s) / polynomial b s) volume 0 v :=
    (show ContinuousOn (fun s => (2 * b + 6 * s) / polynomial b s) (uIcc 0 v) from
      fun s hs => (integrand_contDiff b hb hb1 (hsub hs)).continuousAt.continuousWithinAt).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => logCoordinate_hasDerivAt b hb hb1 (hsub hs)) hi
  simpa [coordinate, logCoordinate] using hftc

private lemma logCoordinate_tendsto (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    Tendsto (logCoordinate b) (𝓝[<] (upperRoot b)) atTop := by
  have hsub : Tendsto (fun v : ℝ => upperRoot b - v)
      (𝓝[<] (upperRoot b)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun v : ℝ => upperRoot b - v) (upperRoot b) :=
        continuousAt_const.sub continuousAt_id
      simpa only [sub_self] using hc.tendsto.mono_left
        (show 𝓝[<] (upperRoot b) ≤ 𝓝 (upperRoot b) from inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact sub_pos.mpr (show v < upperRoot b from hv)
  have hlog : Tendsto (fun v => Real.log (upperRoot b - v))
      (𝓝[<] (upperRoot b)) atBot := Real.tendsto_log_nhdsGT_zero.comp hsub
  have hfirst : Tendsto (fun v => logCoefficient b *
      (Real.log (upperRoot b) - Real.log (upperRoot b - v)))
      (𝓝[<] (upperRoot b)) atTop := by
    apply Tendsto.const_mul_atTop (logCoefficient_pos b hb hb1)
    simpa only [sub_eq_add_neg, add_comm, Function.comp_def] using
      (tendsto_neg_atBot_atTop.comp hlog).atTop_add
        (tendsto_const_nhds (x := Real.log (upperRoot b)))
  have hsecond : ContinuousAt (fun v : ℝ => (logCoefficient b - 1) *
      (Real.log (v + lowerRoot b) - Real.log (lowerRoot b))) (upperRoot b) := by
    apply ContinuousAt.const_mul
    exact (((continuousAt_id.add_const _).log
      (ne_of_gt (add_pos (roots b hb hb1).1 (roots b hb hb1).2.1))).sub_const _)
  exact hfirst.atTop_add (hsecond.tendsto.mono_left inf_le_left)

private lemma coordinate_tendsto (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    Tendsto (coordinate b) (𝓝[<] (upperRoot b)) atTop := by
  apply (logCoordinate_tendsto b hb hb1).congr'
  have hlow : ∀ᶠ v : ℝ in 𝓝[<] (upperRoot b), -radius b < v :=
    (eventually_gt_nhds (show -radius b < upperRoot b by
      linarith [(radius_pos b hb hb1), (roots b hb hb1).1])).filter_mono inf_le_left
  filter_upwards [hlow, self_mem_nhdsWithin] with v hv1 hv2
  exact (coordinate_eq_logCoordinate b hb hb1 ⟨hv1, hv2⟩).symm

lemma coordinate_surj_from (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {a t : ℝ} (ha : a ∈ coordinateDomain b) (ht : coordinate b a ≤ t) : ∃ v ∈ coordinateDomain b, coordinate b v = t := by
  have hcont : ContinuousOn (coordinate b) (coordinateDomain b) :=
    fun v hv => (coordinate_hasDerivAt b hb hb1 hv).continuousAt.continuousWithinAt
  have hfilter : 𝓝[<] (upperRoot b) ≤ 𝓟 (coordinateDomain b) := by
    apply le_principal_iff.mpr
    have hlow : ∀ᶠ v : ℝ in 𝓝[<] (upperRoot b), -radius b < v :=
      (eventually_gt_nhds (show -radius b < upperRoot b by
        linarith [(radius_pos b hb hb1), (roots b hb hb1).1])).filter_mono inf_le_left
    filter_upwards [hlow, self_mem_nhdsWithin] with v hv1 hv2
    exact ⟨hv1, hv2⟩
  exact isPreconnected_Ioo.intermediate_value_Ici ha
    hfilter hcont (coordinate_tendsto b hb hb1) ht

end D5.S3.Analytic.Variational.JointReciprocalFunctional
