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
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
  AEMeasurable u (volume.restrict (Icc (1 : ℝ) 2)) ∧
    ∃ c B : ℝ, 0 < c ∧
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
  · change ContDiffAt ℝ ∞ (fun s : ℝ => 2 * b + 3 * (1 - b) * s - 6 * s ^ 2) v
    fun_prop
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
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun s hs => (integrand_contDiff b hb hb1 hs).continuousAt) v hv) (integrand_contDiff b hb hb1 hv).continuousAt

private lemma coordinate_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
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

private lemma coordinate_strictMono (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
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

private lemma coordinate_surj_from (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
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

/-- The scalar equation has exactly one root in the full original open interval. -/
theorem exists_unique_scalar_root (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃! v : ℝ, 0 < v ∧ v < upperRoot b ∧ coordinate b v = Real.log 2 := by
  obtain ⟨v, hv, heq⟩ := coordinate_surj_from b hb hb1
    (domain_zero b hb hb1) (t := Real.log 2) (by simpa [coordinate] using
      (Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)))
  have hvpos : 0 < v := by
    by_contra h
    have hle := (coordinate_strictMono b hb hb1).monotoneOn hv (domain_zero b hb hb1)
      (le_of_not_gt h)
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hzero : coordinate b 0 = 0 := by simp [coordinate]
    rw [heq, hzero] at hle
    exact (not_le_of_gt hlog) hle
  refine ⟨v, ⟨hvpos, hv.2, heq⟩, ?_⟩
  intro q hq
  apply (coordinate_strictMono b hb hb1).injOn
    ⟨by linarith [radius_pos b hb hb1], hq.2.1⟩ hv
  exact hq.2.2.trans heq.symm

private def inverseCoordinate (b : ℝ) : ℝ → ℝ :=
  Function.invFunOn (coordinate b) (coordinateDomain b)

private lemma inverse_left (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    inverseCoordinate b (coordinate b v) = v :=
  (coordinate_strictMono b hb hb1).injOn.leftInvOn_invFunOn hv

private lemma inverse_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    HasDerivAt (inverseCoordinate b)
      (((2 * b + 6 * v) / polynomial b v)⁻¹) (coordinate b v) := by
  have hd := coordinate_hasDerivAt b hb hb1 hv
  have hc := coordinate_contDiff b hb hb1 hv
  have hp := domain_positive b hb hb1 hv
  have hl : ∀ᶠ s in 𝓝 v, inverseCoordinate b (coordinate b s) = s := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with s hs
    exact inverse_left b hb hb1 hs
  exact ((hc.hasStrictDerivAt' hd (by simp)).to_local_left_inverse
    (ne_of_gt (div_pos hp.2.1 hp.1)) hl).hasDerivAt

private lemma inverse_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {v : ℝ} (hv : v ∈ coordinateDomain b) :
    ContDiffAt ℝ ∞ (inverseCoordinate b) (coordinate b v) := by
  have hd := coordinate_hasDerivAt b hb hb1 hv
  have hc := coordinate_contDiff b hb hb1 hv
  have hp := domain_positive b hb hb1 hv
  have hne := ne_of_gt (div_pos hp.2.1 hp.1)
  have hfd := hd.hasFDerivAt_equiv hne
  have hl : ∀ᶠ s in 𝓝 v, inverseCoordinate b (coordinate b s) = s := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with s hs
    exact inverse_left b hb hb1 hs
  have heq := (hc.hasStrictFDerivAt' hfd (by simp)).localInverse_unique hl
  exact (hc.to_localInverse hfd (by simp)).congr_of_eventuallyEq heq

private def leftLevel (b : ℝ) : ℝ := coordinate b (-radius b / 2)
private def optimizerDomain (b : ℝ) : Set ℝ := Ioi (Real.exp (leftLevel b))

private lemma left_anchor_mem (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    -radius b / 2 ∈ coordinateDomain b := by
  have hr := radius_pos b hb hb1
  have hn := (roots b hb hb1).1
  constructor <;> linarith

private lemma leftLevel_neg (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) : leftLevel b < 0 := by
  have h := coordinate_strictMono b hb hb1 (left_anchor_mem b hb hb1)
    (domain_zero b hb hb1) (by linarith [radius_pos b hb hb1])
  simpa [leftLevel, coordinate] using h

private lemma optimizerDomain_contains (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    Icc (1 : ℝ) 2 ⊆ optimizerDomain b := by
  have h : Real.exp (leftLevel b) < 1 := by
    simpa using Real.exp_lt_exp.mpr (leftLevel_neg b hb hb1)
  intro x hx
  exact h.trans_le hx.1

private def curve (b x : ℝ) : ℝ := inverseCoordinate b (Real.log x)

private lemma curve_spec (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    curve b x ∈ coordinateDomain b ∧ coordinate b (curve b x) = Real.log x := by
  have hxpos : 0 < x := (Real.exp_pos _).trans hx
  have hlog : leftLevel b < Real.log x := (Real.lt_log_iff_exp_lt hxpos).2 hx
  exact Function.invFunOn_pos (coordinate_surj_from b hb hb1
    (left_anchor_mem b hb hb1) (le_of_lt hlog))

private lemma curve_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) : ContDiffAt ℝ ∞ (curve b) x := by
  have hs := curve_spec b hb hb1 hx
  have hi := inverse_contDiff b hb hb1 hs.1
  rw [hs.2] at hi
  exact hi.comp x ((Real.contDiffAt_log).2 (ne_of_gt ((Real.exp_pos _).trans hx)))

private lemma curve_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    HasDerivAt (curve b)
      (polynomial b (curve b x) / (x * (2 * b + 6 * curve b x))) x := by
  have hs := curve_spec b hb hb1 hx
  have hi := inverse_hasDerivAt b hb hb1 hs.1
  rw [hs.2] at hi
  have hp := domain_positive b hb hb1 hs.1
  have hxne : x ≠ 0 := ne_of_gt ((Real.exp_pos _).trans hx)
  convert hi.comp x (Real.hasDerivAt_log hxne) using 1
  · rfl
  · change polynomial b (curve b x) / (x * (2 * b + 6 * curve b x)) =
      ((2 * b + 6 * curve b x) / polynomial b (curve b x))⁻¹ * x⁻¹
    field_simp
    <;> ring

private lemma curve_one (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) : curve b 1 = 0 := by
  have h := inverse_left b hb hb1 (domain_zero b hb hb1)
  simpa [curve, coordinate] using h

/-- The endpoint selected by the original integral equation. -/
def scalarRoot (b : ℝ) : ℝ := curve b 2

/-- The exact candidate value, expressed in the unique scalar root. -/
def sharpConstant (b : ℝ) : ℝ := 8 * scalarRoot b ^ 2 * (b + 2 * scalarRoot b)

private lemma scalarRoot_spec (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 < scalarRoot b ∧ scalarRoot b < upperRoot b ∧
      coordinate b (scalarRoot b) = Real.log 2 := by
  obtain ⟨v, hv, _⟩ := exists_unique_scalar_root b hb hb1
  have hvdom : v ∈ coordinateDomain b :=
    ⟨by linarith [radius_pos b hb hb1, hv.1], hv.2.1⟩
  have hi := inverse_left b hb hb1 hvdom
  rw [hv.2.2] at hi
  change curve b 2 = v at hi
  simpa [scalarRoot, hi] using hv

/-- An algebraically specified extremal, with no normalization or ODE hypothesis. -/
def optimizer (b x : ℝ) : ℝ :=
  x ^ 2 * polynomial b (curve b x) /
    (8 * scalarRoot b * polynomial b (scalarRoot b))

private lemma optimizer_pos (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) : 0 < optimizer b x := by
  have hp := (domain_positive b hb hb1 (curve_spec b hb hb1 hx).1).1
  have hr := scalarRoot_spec b hb hb1
  have hpr := (domain_positive b hb hb1
    (show scalarRoot b ∈ coordinateDomain b from
      ⟨by linarith [radius_pos b hb hb1, hr.1], hr.2.1⟩)).1
  dsimp [optimizer]
  exact div_pos (mul_pos (sq_pos_of_pos ((Real.exp_pos _).trans hx)) hp)
    (mul_pos (mul_pos (by norm_num) hr.1) hpr)

private lemma optimizer_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) : ContDiffAt ℝ ∞ (optimizer b) x := by
  have hcurve := curve_contDiff b hb hb1 hx
  change ContDiffAt ℝ ∞ (fun t : ℝ =>
    t ^ 2 * (2 * b + 3 * (1 - b) * curve b t - 6 * curve b t ^ 2) /
      (8 * scalarRoot b * polynomial b (scalarRoot b))) x
  fun_prop

private lemma normalizer_pos (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 < 8 * scalarRoot b * polynomial b (scalarRoot b) := by
  have hr := scalarRoot_spec b hb hb1
  have hp := (domain_positive b hb hb1
    (show scalarRoot b ∈ coordinateDomain b from
      ⟨by linarith [radius_pos b hb hb1, hr.1], hr.2.1⟩)).1
  exact mul_pos (mul_pos (by norm_num) hr.1) hp

private lemma polynomial_hasDerivAt (b v : ℝ) :
    HasDerivAt (polynomial b) (3 * (1 - b) - 12 * v) v := by
  convert ((hasDerivAt_const v (2 * b)).add
    ((hasDerivAt_id v).const_mul (3 * (1 - b)))).sub
      ((hasDerivAt_pow 2 v).const_mul 6) using 1
  · funext t; dsimp [polynomial] <;> ring
  · norm_num <;> ring

private lemma optimizer_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    HasDerivAt (optimizer b)
      ((b + 3) * optimizer b x / (x * (2 * b + 6 * curve b x))) x := by
  have hc := curve_hasDerivAt b hb hb1 hx
  have hp := (polynomial_hasDerivAt b (curve b x)).comp x hc
  have hw := ((hasDerivAt_pow 2 x).mul hp).div_const
    (8 * scalarRoot b * polynomial b (scalarRoot b))
  have hxne : x ≠ 0 := ne_of_gt ((Real.exp_pos _).trans hx)
  have hn := ne_of_gt (normalizer_pos b hb hb1)
  have hd := ne_of_gt (domain_positive b hb hb1 (curve_spec b hb hb1 hx).1).2.1
  convert hw using 1
  · rfl
  · have hrne := ne_of_gt (scalarRoot_spec b hb hb1).1
    have hprne := (mul_ne_zero_iff.mp hn).2
    dsimp only [optimizer, Function.comp_apply, Pi.mul_apply, Pi.add_apply,
      Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp [hrne, hprne, hd, hxne]
    dsimp [polynomial]
    ring_nf
    field_simp [show b * 2 + curve b x * 6 ≠ 0 by intro he; apply hd; linarith only [he],
      show curve b x * 6 + b * 2 ≠ 0 by intro he; apply hd; linarith only [he]]
    <;> ring

private def profilePrimitive (b x : ℝ) : ℝ := x * optimizer b x * curve b x

private lemma profile_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    HasDerivAt (profilePrimitive b) (optimizer b x) x := by
  have hc := curve_hasDerivAt b hb hb1 hx
  have hw := optimizer_hasDerivAt b hb hb1 hx
  have hxne : x ≠ 0 := ne_of_gt ((Real.exp_pos _).trans hx)
  have hd := ne_of_gt (domain_positive b hb hb1 (curve_spec b hb hb1 hx).1).2.1
  convert ((hasDerivAt_id x).mul hw).mul hc using 1
  · rfl
  · dsimp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq,
      Function.comp_apply]
    field_simp [hd, hxne]
    dsimp [polynomial]
    ring_nf
    field_simp [show b * 2 + curve b x * 6 ≠ 0 by intro he; apply hd; linarith only [he],
      show curve b x * 6 + b * 2 ≠ 0 by intro he; apply hd; linarith only [he]]
    <;> ring

private lemma primitive_eq_profile (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    primitive (optimizer b) x = profilePrimitive b x := by
  have h1 : (1 : ℝ) ∈ optimizerDomain b := optimizerDomain_contains b hb hb1 (by norm_num)
  have hsub : uIcc 1 x ⊆ optimizerDomain b := ordConnected_Ioi.uIcc_subset h1 hx
  have hi : IntervalIntegrable (optimizer b) volume 1 x :=
    (show ContinuousOn (optimizer b) (uIcc 1 x) from
      fun t ht => (optimizer_contDiff b hb hb1 (hsub ht)).continuousAt.continuousWithinAt).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => profile_hasDerivAt b hb hb1 (hsub ht)) hi
  simpa [primitive, profilePrimitive, curve_one b hb hb1] using hftc

private lemma optimizer_two (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    optimizer b 2 = 1 / (2 * scalarRoot b) := by
  have hr := scalarRoot_spec b hb hb1
  have hp := ne_of_gt (domain_positive b hb hb1
    (show scalarRoot b ∈ coordinateDomain b from
      ⟨by linarith [radius_pos b hb hb1, hr.1], hr.2.1⟩)).1
  change 2 ^ 2 * polynomial b (scalarRoot b) /
    (8 * scalarRoot b * polynomial b (scalarRoot b)) = 1 / (2 * scalarRoot b)
  field_simp
  <;> ring

private lemma optimizer_mass (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    mass (optimizer b) = 1 := by
  have h2 : (2 : ℝ) ∈ optimizerDomain b := optimizerDomain_contains b hb hb1 (by norm_num)
  change primitive (optimizer b) 2 = 1
  rw [primitive_eq_profile b hb hb1 h2]
  dsimp only [profilePrimitive]
  rw [optimizer_two b hb hb1]
  change 2 * (1 / (2 * scalarRoot b)) * scalarRoot b = 1
  field_simp [ne_of_gt (scalarRoot_spec b hb hb1).1]

private def costPrimitive (b x : ℝ) : ℝ :=
  x ^ 2 * (b * curve b x + 2 * curve b x ^ 2) / optimizer b x

private lemma costPrimitive_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    HasDerivAt (costPrimitive b)
      (b * (x / optimizer b x) + profilePrimitive b x / optimizer b x ^ 2) x := by
  have hc := curve_hasDerivAt b hb hb1 hx
  have hw := optimizer_hasDerivAt b hb hb1 hx
  have hwne := ne_of_gt (optimizer_pos b hb hb1 hx)
  have hxne : x ≠ 0 := ne_of_gt ((Real.exp_pos _).trans hx)
  have hd := ne_of_gt (domain_positive b hb hb1 (curve_spec b hb hb1 hx).1).2.1
  have hnum := (hasDerivAt_pow 2 x).mul
    ((hc.const_mul b).add ((hc.pow 2).const_mul 2))
  convert hnum.div hw hwne using 1
  · rfl
  · dsimp only [profilePrimitive, Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
      Pi.pow_apply, id_eq, Function.comp_apply]
    field_simp [hd, hxne, hwne]
    dsimp [polynomial]
    ring_nf
    field_simp [show b * 2 + curve b x * 6 ≠ 0 by intro he; apply hd; linarith only [he],
      show curve b x * 6 + b * 2 ≠ 0 by intro he; apply hd; linarith only [he]]
    <;> ring

private lemma admissible_integrability {u : ℝ → ℝ} (hu : Admissible u) :
    IntervalIntegrable u volume 1 2 ∧
    IntervalIntegrable (fun x => x / u x) volume 1 2 ∧
    IntervalIntegrable (fun x => primitive u x / u x ^ 2) volume 1 2 := by
  obtain ⟨c, B, hc, hbounds⟩ := hu.2
  have hi : IntegrableOn u (Icc (1 : ℝ) 2) volume :=
    Integrable.of_bound hu.1.aestronglyMeasurable B (hbounds.mono fun x hx => by
      rw [Real.norm_of_nonneg (by linarith [hx.1])]
      exact hx.2)
  have hii : IntervalIntegrable u volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hi
  have huc : ContinuousOn (primitive u) (Icc (1 : ℝ) 2) := by
    change ContinuousOn (fun x : ℝ => ∫ t in (1 : ℝ)..x, u t) (Icc (1 : ℝ) 2)
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ))
      hii left_mem_uIcc
    rw [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] at h
    exact h
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
  have hlag : IntegrableOn (fun x => x / u x) (Icc (1 : ℝ) 2) volume := by
    apply Integrable.of_bound
      (measurable_id.aemeasurable.div hu.1).aestronglyMeasurable (2 / c)
    filter_upwards [hbounds, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    have hup : 0 < u x := hc.trans_le hx.1
    change ‖x / u x‖ ≤ 2 / c
    rw [norm_div, Real.norm_of_nonneg (by linarith [hxmem.1]),
      Real.norm_of_nonneg hup.le]
    apply (div_le_div_iff₀ hup hc).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hxmem.2) hc.le]
  have hfuture : IntegrableOn (fun x => primitive u x / u x ^ 2)
      (Icc (1 : ℝ) 2) volume := by
    have hmeas : AEMeasurable (primitive u) (volume.restrict (Icc (1 : ℝ) 2)) :=
      (huc.aestronglyMeasurable measurableSet_Icc).aemeasurable
    apply Integrable.of_bound (hmeas.div (hu.1.pow_const 2)).aestronglyMeasurable
      (M / c ^ 2)
    filter_upwards [hbounds, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    have hup : 0 < u x := hc.trans_le hx.1
    have hsq : c ^ 2 ≤ u x ^ 2 := by nlinarith [hx.1]
    change ‖primitive u x / u x ^ 2‖ ≤ M / c ^ 2
    rw [norm_div, norm_pow, Real.norm_of_nonneg hup.le]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hc) hsq).trans
      (div_le_div_of_nonneg_right (hM x hxmem) (sq_nonneg c))
  exact ⟨hii,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hlag,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hfuture⟩

private lemma optimizer_admissible (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    Admissible (optimizer b) := by
  have hsub := optimizerDomain_contains b hb hb1
  have hc : ContinuousOn (optimizer b) (Icc (1 : ℝ) 2) :=
    fun x hx => (optimizer_contDiff b hb hb1 (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (show (Icc (1 : ℝ) 2).Nonempty by
    exact ⟨1, by norm_num⟩) hc
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (show (Icc (1 : ℝ) 2).Nonempty by
    exact ⟨1, by norm_num⟩) hc
  refine ⟨(hc.aestronglyMeasurable measurableSet_Icc).aemeasurable,
    optimizer b x, optimizer b y, optimizer_pos b hb hb1 (hsub hx), ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact ⟨hmin ht, hmax ht⟩

private lemma optimizer_cost (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    cost b (optimizer b) = sharpConstant b := by
  have hsub := optimizerDomain_contains b hb hb1
  have hdata := admissible_integrability (optimizer_admissible b hb hb1)
  have hlag := hdata.2.1
  have hfuture : IntervalIntegrable
      (fun x => profilePrimitive b x / optimizer b x ^ 2) volume 1 2 := by
    apply hdata.2.2.congr
    intro x hx
    change primitive (optimizer b) x / optimizer b x ^ 2 =
      profilePrimitive b x / optimizer b x ^ 2
    rw [primitive_eq_profile b hb hb1
      (hsub (Ioc_subset_Icc_self
        (show x ∈ Ioc (1 : ℝ) 2 by simpa only [uIoc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using hx)))]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => costPrimitive_hasDerivAt b hb hb1
      (hsub (by simpa only [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using hx)))
    ((hlag.const_mul b).add hfuture)
  have hcost : cost b (optimizer b) =
      ∫ x in (1 : ℝ)..2,
        b * (x / optimizer b x) + profilePrimitive b x / optimizer b x ^ 2 := by
    dsimp only [cost]
    rw [intervalIntegral.integral_add (hlag.const_mul b) hfuture,
      intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    change primitive (optimizer b) x / optimizer b x ^ 2 =
      profilePrimitive b x / optimizer b x ^ 2
    rw [primitive_eq_profile b hb hb1
      (hsub (by simpa only [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using hx))]
  rw [hcost, hftc]
  dsimp only [costPrimitive]
  rw [curve_one b hb hb1, optimizer_two b hb hb1]
  dsimp only [sharpConstant, scalarRoot]
  field_simp
  <;> ring

/-- The explicitly constructed profile is smooth, strictly increasing, normalized,
and has the exact cost. Global minimality requires the measurable comparison. -/
theorem constructed_profile (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 < scalarRoot b ∧ scalarRoot b < upperRoot b ∧
    coordinate b (scalarRoot b) = Real.log 2 ∧ 0 < sharpConstant b ∧
    ∃ s : Set ℝ, IsOpen s ∧ Icc (1 : ℝ) 2 ⊆ s ∧
      ContDiffOn ℝ ∞ (optimizer b) s ∧
      (∀ x ∈ s, 0 < optimizer b x) ∧ StrictMonoOn (optimizer b) s ∧
      Admissible (optimizer b) ∧ mass (optimizer b) = 1 ∧
      cost b (optimizer b) = sharpConstant b := by
  have hr := scalarRoot_spec b hb hb1
  refine ⟨hr.1, hr.2.1, hr.2.2, ?_, optimizerDomain b, isOpen_Ioi,
    optimizerDomain_contains b hb hb1,
    (fun x hx => (optimizer_contDiff b hb hb1 hx).contDiffWithinAt),
    (fun x hx => optimizer_pos b hb hb1 hx), ?_, optimizer_admissible b hb hb1,
    optimizer_mass b hb hb1, optimizer_cost b hb hb1⟩
  · dsimp only [sharpConstant]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hr.1)) (by linarith [hr.1])
  · apply strictMonoOn_of_deriv_pos (convex_Ioi _)
    · exact fun x hx => (optimizer_contDiff b hb hb1 hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(optimizer_hasDerivAt b hb hb1 hx').deriv]
      exact div_pos (mul_pos (by linarith) (optimizer_pos b hb hb1 hx'))
        (mul_pos ((Real.exp_pos _).trans hx')
          (domain_positive b hb hb1 (curve_spec b hb hb1 hx').1).2.1)

private lemma profile_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    ContDiffAt ℝ ∞ (profilePrimitive b) x := by
  exact (contDiffAt_id.mul (optimizer_contDiff b hb hb1 hx)).mul
    (curve_contDiff b hb hb1 hx)

private lemma profile_strictMono (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    StrictMonoOn (profilePrimitive b) (optimizerDomain b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · exact fun x hx => (profile_contDiff b hb hb1 hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [(profile_hasDerivAt b hb hb1 (interior_subset hx)).deriv]
    exact optimizer_pos b hb hb1 (interior_subset hx)

private def massDomain (b : ℝ) : Set ℝ := profilePrimitive b '' optimizerDomain b
private def inverseMass (b : ℝ) : ℝ → ℝ :=
  Function.invFunOn (profilePrimitive b) (optimizerDomain b)

private lemma inverseMass_left (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    inverseMass b (profilePrimitive b x) = x :=
  (profile_strictMono b hb hb1).injOn.leftInvOn_invFunOn hx

private lemma inverseMass_spec (b : ℝ) {r : ℝ} (hr : r ∈ massDomain b) :
    inverseMass b r ∈ optimizerDomain b ∧ profilePrimitive b (inverseMass b r) = r :=
  Function.invFunOn_pos hr

private lemma inverseMass_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    HasDerivAt (inverseMass b) (optimizer b x)⁻¹ (profilePrimitive b x) := by
  have hd := profile_hasDerivAt b hb hb1 hx
  have hc := profile_contDiff b hb hb1 hx
  have hl : ∀ᶠ s in 𝓝 x, inverseMass b (profilePrimitive b s) = s := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with s hs
    exact inverseMass_left b hb hb1 hs
  exact ((hc.hasStrictDerivAt' hd (by simp)).to_local_left_inverse
    (ne_of_gt (optimizer_pos b hb hb1 hx)) hl).hasDerivAt

private lemma inverseMass_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    ContDiffAt ℝ ∞ (inverseMass b) (profilePrimitive b x) := by
  have hd := profile_hasDerivAt b hb hb1 hx
  have hc := profile_contDiff b hb hb1 hx
  have hfd := hd.hasFDerivAt_equiv (ne_of_gt (optimizer_pos b hb hb1 hx))
  have hl : ∀ᶠ s in 𝓝 x, inverseMass b (profilePrimitive b s) = s := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with s hs
    exact inverseMass_left b hb hb1 hs
  have heq := (hc.hasStrictFDerivAt' hfd (by simp)).localInverse_unique hl
  exact (hc.to_localInverse hfd (by simp)).congr_of_eventuallyEq heq

private lemma massDomain_open (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    IsOpen (massDomain b) := by
  rw [isOpen_iff_mem_nhds]
  rintro r ⟨x, hx, rfl⟩
  have h := ((profile_contDiff b hb hb1 hx).hasStrictDerivAt'
    (profile_hasDerivAt b hb hb1 hx) (by simp)).map_nhds_eq
    (ne_of_gt (optimizer_pos b hb hb1 hx))
  rw [← h]
  exact image_mem_map (isOpen_Ioi.mem_nhds hx)

private lemma profile_one (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    profilePrimitive b 1 = 0 := by simp [profilePrimitive, curve_one b hb hb1]

private lemma profile_two (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    profilePrimitive b 2 = 1 := by
  rw [← primitive_eq_profile b hb hb1
    (optimizerDomain_contains b hb hb1 (by norm_num))]
  exact optimizer_mass b hb hb1

private lemma massDomain_contains (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    Icc (0 : ℝ) 1 ⊆ massDomain b := by
  have hc : ContinuousOn (profilePrimitive b) (Icc (1 : ℝ) 2) :=
    fun x hx => (profile_contDiff b hb hb1
      (optimizerDomain_contains b hb hb1 hx)).continuousAt.continuousWithinAt
  have hi := intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num) hc
  rw [profile_one b hb hb1, profile_two b hb hb1] at hi
  intro r hr
  obtain ⟨x, hx, heq⟩ := hi hr
  exact ⟨x, optimizerDomain_contains b hb hb1 hx, heq⟩

private def spaceCoordinate (x : ℝ) : ℝ := x * Real.sqrt x
private def slopeCoefficient (b x : ℝ) : ℝ :=
  4 * b * Real.sqrt x / (3 * optimizer b x) +
    2 * profilePrimitive b x / (Real.sqrt x * optimizer b x ^ 2)
private def valueCoefficient (b x : ℝ) : ℝ :=
  -(profilePrimitive b x) / (x * Real.sqrt x * optimizer b x ^ 3)
private def referenceCoordinate (b r : ℝ) : ℝ := spaceCoordinate (inverseMass b r)
private def referenceSlope (b r : ℝ) : ℝ :=
  3 * Real.sqrt (inverseMass b r) / (2 * optimizer b (inverseMass b r))
private def calibrationSlope (b r : ℝ) : ℝ := slopeCoefficient b (inverseMass b r)
private def calibrationValue (b r : ℝ) : ℝ := valueCoefficient b (inverseMass b r)

private lemma spaceCoordinate_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt spaceCoordinate (3 * Real.sqrt x / 2) x := by
  have hs := Real.sq_sqrt hx.le
  convert (hasDerivAt_id x).mul (Real.hasDerivAt_sqrt (ne_of_gt hx)) using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hx)]
    nlinarith

private lemma slopeCoefficient_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    HasDerivAt (slopeCoefficient b)
      (optimizer b x * valueCoefficient b x) x := by
  have hw := optimizer_hasDerivAt b hb hb1 hx
  have hW := profile_hasDerivAt b hb hb1 hx
  have hxpos := (Real.exp_pos _).trans hx
  have hs := Real.hasDerivAt_sqrt (ne_of_gt hxpos)
  have hwne := ne_of_gt (optimizer_pos b hb hb1 hx)
  have hsne := ne_of_gt (Real.sqrt_pos.2 hxpos)
  have hd := ne_of_gt (domain_positive b hb hb1 (curve_spec b hb hb1 hx).1).2.1
  have h := ((hs.const_mul (4 * b)).div (hw.const_mul 3)
    (mul_ne_zero (by norm_num) hwne)).add
    ((hW.const_mul 2).div (hs.mul (hw.pow 2))
      (mul_ne_zero hsne (pow_ne_zero 2 hwne)))
  convert h using 1
  · rfl
  · dsimp only [valueCoefficient, profilePrimitive, Pi.mul_apply, Pi.pow_apply]
    norm_num only [Nat.cast_ofNat, pow_one, Nat.reduceSub]
    field_simp [hwne, hsne, hd, ne_of_gt hxpos]
    ring_nf
    field_simp [show b * 2 + curve b x * 6 ≠ 0 by intro he; apply hd; linarith only [he],
      show curve b x * 6 + b * 2 ≠ 0 by intro he; apply hd; linarith only [he]]
    have hsq := Real.sq_sqrt hxpos.le
    generalize Real.sqrt x = t at *
    rw [← hsq]
    ring

private lemma calibrationSlope_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {r : ℝ} (hr : r ∈ massDomain b) :
    HasDerivAt (calibrationSlope b) (calibrationValue b r) r := by
  have hx := inverseMass_spec b hr
  have hi := inverseMass_hasDerivAt b hb hb1 hx.1
  rw [hx.2] at hi
  convert (slopeCoefficient_hasDerivAt b hb hb1 hx.1).comp r hi using 1
  · rfl
  · dsimp only [calibrationValue]
    field_simp [ne_of_gt (optimizer_pos b hb hb1 hx.1)]

private lemma referenceCoordinate_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {r : ℝ} (hr : r ∈ massDomain b) :
    HasDerivAt (referenceCoordinate b) (referenceSlope b r) r := by
  have hx := inverseMass_spec b hr
  have hi := inverseMass_hasDerivAt b hb hb1 hx.1
  rw [hx.2] at hi
  convert (spaceCoordinate_hasDerivAt ((Real.exp_pos _).trans hx.1)).comp r hi using 1
  · rfl
  · dsimp only [referenceSlope]
    ring

private lemma calibrationSlope_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {r : ℝ} (hr : r ∈ massDomain b) : ContDiffAt ℝ ∞ (calibrationSlope b) r := by
  have hx := inverseMass_spec b hr
  have hi := inverseMass_contDiff b hb hb1 hx.1
  rw [hx.2] at hi
  have hs := Real.contDiffAt_sqrt (n := ∞) (ne_of_gt ((Real.exp_pos _).trans hx.1))
  have hw := optimizer_contDiff b hb hb1 hx.1
  have hW := profile_contDiff b hb hb1 hx.1
  have hwne := ne_of_gt (optimizer_pos b hb hb1 hx.1)
  have hsne := ne_of_gt (Real.sqrt_pos.2 ((Real.exp_pos _).trans hx.1))
  have hc : ContDiffAt ℝ ∞ (slopeCoefficient b) (inverseMass b r) :=
    ((contDiffAt_const.mul hs).div (contDiffAt_const.mul hw)
      (mul_ne_zero (by norm_num) hwne)).add
      ((contDiffAt_const.mul hW).div (hs.mul (hw.pow 2))
        (mul_ne_zero hsne (pow_ne_zero 2 hwne)))
  exact hc.comp r hi

private lemma referenceCoordinate_contDiff (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {r : ℝ} (hr : r ∈ massDomain b) : ContDiffAt ℝ ∞ (referenceCoordinate b) r := by
  have hx := inverseMass_spec b hr
  have hi := inverseMass_contDiff b hb hb1 hx.1
  rw [hx.2] at hi
  exact (contDiffAt_id.mul (Real.contDiffAt_sqrt
    (ne_of_gt ((Real.exp_pos _).trans hx.1)))).comp r hi

private lemma functional_support {b r z q Z Q : ℝ} (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hz : 0 < z) (hq : 0 ≤ q) (hZ : 0 < Z) (hQ : 0 < Q) :
    (-8 * r * Q ^ 3 / (27 * Z ^ 2)) * z +
      (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * q -
      ((-8 * r * Q ^ 3 / (27 * Z ^ 2)) * Z +
        (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * Q) / 2 ≤
      4 * b * q ^ 2 / 9 + 8 * r * q ^ 3 / (27 * z) := by
  have hp : 0 ≤ q ^ 3 * Z ^ 2 + Q ^ 3 * z ^ 2 + Q ^ 3 * z * Z -
      3 * Q ^ 2 * q * z * Z := by
    by_cases h : q ≤ Q / 3
    · have hn : 0 ≤ Q ^ 2 * z * Z * (Q - 3 * q) := by
        apply mul_nonneg (by positivity) (by linarith)
      nlinarith [mul_nonneg (pow_nonneg hq 3) (sq_nonneg Z),
        mul_nonneg (pow_nonneg hQ.le 3) (sq_nonneg z)]
    · have hn : 0 ≤ Q * (2 * Q * z - 3 * q * Z + Q * Z) ^ 2 +
          Z ^ 2 * (q - Q) ^ 2 * (4 * q - Q) := by
        apply add_nonneg (by positivity)
        exact mul_nonneg (mul_nonneg (sq_nonneg Z) (sq_nonneg (q - Q)))
          (by linarith)
      have he : 4 * (q ^ 3 * Z ^ 2 + Q ^ 3 * z ^ 2 + Q ^ 3 * z * Z -
          3 * Q ^ 2 * q * z * Z) =
          Q * (2 * Q * z - 3 * q * Z + Q * Z) ^ 2 +
            Z ^ 2 * (q - Q) ^ 2 * (4 * q - Q) := by ring
      linarith
  have hg : 0 ≤ q ^ 3 / z -
      (Q ^ 3 / Z - Q ^ 3 / Z ^ 2 * (z - Z) + 3 * Q ^ 2 / Z * (q - Q)) := by
    apply nonneg_of_mul_nonneg_right (a := z * Z ^ 2) ?_ (by positivity)
    convert hp using 1 <;> field_simp <;> ring
  have hn := add_nonneg
    (mul_nonneg (show 0 ≤ 4 * b / 9 by positivity) (sq_nonneg (q - Q)))
    (mul_nonneg (show 0 ≤ 8 * r / 27 by positivity) hg)
  have he : 4 * b * q ^ 2 / 9 + 8 * r * q ^ 3 / (27 * z) -
      ((-8 * r * Q ^ 3 / (27 * Z ^ 2)) * z +
        (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * q -
        ((-8 * r * Q ^ 3 / (27 * Z ^ 2)) * Z +
          (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * Q) / 2) =
      4 * b / 9 * (q - Q) ^ 2 + 8 * r / 27 *
        (q ^ 3 / z - (Q ^ 3 / Z - Q ^ 3 / Z ^ 2 * (z - Z) +
          3 * Q ^ 2 / Z * (q - Q))) := by field_simp; ring
  linarith

private lemma calibration_coefficients (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {r : ℝ} (hr : r ∈ massDomain b) :
    0 < referenceCoordinate b r ∧ 0 < referenceSlope b r ∧
    calibrationSlope b r = 8 * b * referenceSlope b r / 9 +
      8 * r * referenceSlope b r ^ 2 / (9 * referenceCoordinate b r) ∧
    calibrationValue b r =
      -8 * r * referenceSlope b r ^ 3 / (27 * referenceCoordinate b r ^ 2) := by
  have hx := inverseMass_spec b hr
  have hy := (Real.exp_pos _).trans hx.1
  have hw := optimizer_pos b hb hb1 hx.1
  have hs := Real.sqrt_pos.2 hy
  refine ⟨mul_pos hy hs, div_pos (by positivity) (by positivity), ?_, ?_⟩
  all_goals
    dsimp only [calibrationSlope, slopeCoefficient, calibrationValue, valueCoefficient,
      referenceSlope, referenceCoordinate, spaceCoordinate]
    rw [hx.2]
    field_simp [ne_of_gt hy, ne_of_gt hw, ne_of_gt hs]
    have hsq := Real.sq_sqrt hy.le
    generalize Real.sqrt (inverseMass b r) = t at *
    rw [← hsq]
    ring

private def profileCalibration (b x : ℝ) : ℝ :=
  slopeCoefficient b x * spaceCoordinate x / 2

private lemma profileCalibration_hasDerivAt (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : ℝ} (hx : x ∈ optimizerDomain b) :
    HasDerivAt (profileCalibration b)
      (b * (x / optimizer b x) + profilePrimitive b x / optimizer b x ^ 2) x := by
  have hy := (Real.exp_pos _).trans hx
  have hw := optimizer_pos b hb hb1 hx
  have hs := Real.sqrt_pos.2 hy
  convert ((slopeCoefficient_hasDerivAt b hb hb1 hx).mul
    (spaceCoordinate_hasDerivAt hy)).div_const 2 using 1
  · rfl
  · dsimp only [slopeCoefficient, valueCoefficient, spaceCoordinate]
    field_simp [ne_of_gt hy, ne_of_gt hw, ne_of_gt hs]
    have hsq := Real.sq_sqrt hy.le
    generalize Real.sqrt x = t at *
    rw [← hsq]
    ring

end D5.S3.Analytic.Variational.JointReciprocalFunctional


