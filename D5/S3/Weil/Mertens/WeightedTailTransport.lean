/- GID: D5/S3/Weil/Mertens/WeightedTailTransport
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/WeightedTailTransport
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Absolute Fubini and exact logarithmic substitution for L1 weighted tails. -/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

import D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent

namespace D5.S3.Weil.Mertens.WeightedTailTransport

open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent

open Real Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The original logarithmic envelope, with no exponential normalization. -/
def r (t : ℝ) : ℝ := (1 + log t) / (log t) ^ 2

/-- Exactly `-r'` on `t > 1`. -/
def density (t : ℝ) : ℝ := (log t + 2) / (t * (log t) ^ 3)



def tail (K : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in Ioi t, K u

def weightedTail (K : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in Ioi t, K u * r u

private lemma r_pos {t : ℝ} (ht : 1 < t) : 0 < r t := by
  have hl : 0 < log t := log_pos ht
  dsimp [r]
  positivity

private lemma neg_r_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun z => -r z) (density t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : log t ≠ 0 := ne_of_gt (log_pos ht)
  have hd := ((Real.hasDerivAt_log ht0).const_add 1).div
    ((Real.hasDerivAt_log ht0).pow 2) (pow_ne_zero 2 hl0)
  change HasDerivAt (fun z : ℝ => -((1 + log z) / (log z) ^ 2)) (density t) t
  convert hd.neg using 1
  dsimp [density]
  field_simp [ht0, hl0]
  ring

private lemma density_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ density t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := log_pos ht
  dsimp [density]
  positivity

private lemma tendsto_neg_r : Tendsto (fun t : ℝ => -r t) atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => (log t)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_log_atTop.inv_tendsto_atTop
  have heq : (fun t : ℝ => -r t) =
      (fun t : ℝ => -((log t)⁻¹ + ((log t)⁻¹) ^ 2)) := by
    funext t
    by_cases hl : log t = 0
    · simp [r, hl]
    · dsimp [r]
      field_simp [hl]
      <;> ring
  rw [heq]
  simpa using (hi.add (hi.pow 2)).neg

/-- Integrability is proved from the nonnegative derivative and its finite limit,
not supplied as an extra budget. -/
private lemma density_integrable {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn density (Ioi t) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun z hz => by
      change t ≤ z at hz
      exact neg_r_hasDerivAt (by linarith))
    (fun z hz => by
      change t < z at hz
      exact density_nonneg (by linarith)) tendsto_neg_r

private lemma density_mass {t : ℝ} (ht : 2 ≤ t) :
    (∫ z in Ioi t, density z) = r t := by
  simpa only [zero_sub, neg_neg] using
    (integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun z hz => by
        change t ≤ z at hz
        exact neg_r_hasDerivAt (by linarith))
      (density_integrable ht) tendsto_neg_r)

private lemma density_interval {t u : ℝ} (ht : 2 ≤ t) (htu : t ≤ u) :
    (∫ z in t..u, density z) = r t - r u := by
  have hi : IntervalIntegrable density volume t u := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htu]
    exact (density_integrable ht).mono_set Ioc_subset_Ioi_self
  have hd : ∀ z ∈ uIcc t u, HasDerivAt (fun x => -r x) (density z) z := by
    intro z hz
    rw [uIcc_of_le htu] at hz
    exact neg_r_hasDerivAt (by linarith [hz.1])
  simpa only [neg_sub_neg] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

private def triangle (K : ℝ → ℝ) (z u : ℝ) : ℝ :=
  {p : ℝ × ℝ | p.1 < p.2}.indicator
    (fun p => density p.1 * K p.2) (z, u)

/-- An indicator of an L1 product is L1. This is absolute Fubini, with only
`K ∈ L1(t,∞)` assumed. In particular the absolute triangular integral is at
most `(∫ density) * (∫ |K|) = r(t) * (∫ |K|) < ∞`. -/
private lemma triangle_integrable {K : ℝ → ℝ} {t : ℝ} (ht : 2 ≤ t)
    (hK : IntegrableOn K (Ioi t)) :
    Integrable (Function.uncurry (triangle K))
      ((volume.restrict (Ioi t)).prod (volume.restrict (Ioi t))) := by
  exact ((density_integrable ht).mul_prod hK).indicator
    (measurableSet_lt measurable_fst measurable_snd)

private lemma triangle_right {K : ℝ → ℝ} {t z : ℝ} (hz : t < z) :
    (∫ u in Ioi t, triangle K z u) = density z * tail K z := by
  have heq : (fun u => triangle K z u) =
      (Ioi z).indicator (fun u => density z * K u) := by
    ext u
    simp only [triangle, indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioi]
  rw [heq, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hz.le), integral_const_mul]
  rfl

private lemma triangle_left {K : ℝ → ℝ} {t u : ℝ} (ht : 2 ≤ t) (hu : t < u) :
    (∫ z in Ioi t, triangle K z u) = K u * (r t - r u) := by
  have heq : (fun z => triangle K z u) =
      (Iio u).indicator (fun z => density z * K u) := by
    ext z
    simp only [triangle, indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio]
  rw [heq, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Ioi_inter_Iio,
    integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hu.le, density_interval ht hu.le]
  ring

/-- Weighted-tail transport for an arbitrary real L1 kernel. Neither
differentiability of K nor integrability of K*r or density*tail is assumed.
Open endpoints are retained throughout, and the finite FTC includes both ends. -/
theorem transport {K : ℝ → ℝ} {t : ℝ} (ht : 2 ≤ t)
    (hK : IntegrableOn K (Ioi t)) :
    IntegrableOn (fun u => K u * r u) (Ioi t) ∧
      IntegrableOn (fun z => density z * tail K z) (Ioi t) ∧
        tail K t * r t - weightedTail K t =
          ∫ z in Ioi t, density z * tail K z := by
  have htri := triangle_integrable ht hK
  have hdelta : IntegrableOn (fun u => K u * (r t - r u)) (Ioi t) := by
    apply htri.integral_prod_right.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact triangle_left ht hu
  have hKr : IntegrableOn (fun u => K u * r u) (Ioi t) := by
    refine (integrableOn_congr_fun
      (f := fun u => K u * r t - K u * (r t - r u))
      (g := fun u => K u * r u) (s := Ioi t) ?_ measurableSet_Ioi).mp ?_
    · intro u hu
      ring
    · exact (hK.mul_const (r t)).sub hdelta
  have hQt : IntegrableOn (fun z => density z * tail K z) (Ioi t) := by
    apply htri.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact triangle_right hz
  refine ⟨hKr, hQt, ?_⟩
  have hswap := integral_integral_swap htri
  have hfirst : (∫ z in Ioi t, ∫ u in Ioi t, triangle K z u) =
      ∫ z in Ioi t, density z * tail K z := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    exact triangle_right hz
  have hsecond : (∫ u in Ioi t, ∫ z in Ioi t, triangle K z u) =
      ∫ u in Ioi t, K u * (r t - r u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact triangle_left ht hu
  rw [hfirst, hsecond] at hswap
  rw [hswap]
  calc
    tail K t * r t - weightedTail K t =
        ∫ u in Ioi t, K u * r t - K u * r u := by
      rw [integral_sub (hK.mul_const (r t)) hKr, integral_mul_const]
      rfl
    _ = ∫ u in Ioi t, K u * (r t - r u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      ring

private lemma r_exp (y : ℝ) : r (exp y) = R y := by
  simp only [r, R, log_exp, add_comm]

/-- The exponential Jacobian cancels the single `1/z` in `-r'(z)`.
There is no factor `exp(-y)` in W or in `tail K (exp y)`. -/
private lemma exp_density (y : ℝ) : exp y * density (exp y) = W y := by
  dsimp [density, W]
  rw [log_exp, ← mul_div_assoc]
  exact mul_div_mul_left (y + 2) (y ^ 3) (exp_ne_zero y)

/-- Exact logarithmic transport in the original normalization. -/
theorem transport_exp {K : ℝ → ℝ} {y : ℝ} (hy : log 2 ≤ y)
    (hK : IntegrableOn K (Ioi (exp y))) :
    IntegrableOn (fun v => W v * tail K (exp v)) (Ioi y) ∧
      R y * (tail K (exp y) - weightedTail K (exp y) / r (exp y)) =
        ∫ v in Ioi y, W v * tail K (exp v) := by
  have ht : (2 : ℝ) ≤ exp y := by
    calc
      2 = exp (log 2) := (exp_log (by norm_num)).symm
      _ ≤ exp y := exp_le_exp.mpr hy
  have htr := transport ht hK
  have hpoint : (fun v : ℝ => exp v • (density (exp v) * tail K (exp v))) =
      (fun v : ℝ => W v * tail K (exp v)) := by
    funext v
    rw [smul_eq_mul, ← mul_assoc, exp_density]
  have hint := (integrableOn_comp_exp_Ioi
    (fun z => density z * tail K z) y).mpr htr.2.1
  rw [hpoint] at hint
  have hsub := integral_comp_exp_Ioi (fun z => density z * tail K z) y
  rw [hpoint] at hsub
  have hr0 : r (exp y) ≠ 0 := ne_of_gt (r_pos (by linarith))
  refine ⟨hint, ?_⟩
  calc
    R y * (tail K (exp y) - weightedTail K (exp y) / r (exp y)) =
        tail K (exp y) * r (exp y) - weightedTail K (exp y) := by
      rw [← r_exp y]
      field_simp [hr0]
      <;> ring
    _ = ∫ z in Ioi (exp y), density z * tail K z := htr.2.2
    _ = ∫ v in Ioi y, W v * tail K (exp v) := hsub.symm

end
end D5.S3.Weil.Mertens.WeightedTailTransport
