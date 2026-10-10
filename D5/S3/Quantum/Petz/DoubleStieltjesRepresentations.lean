/- GID: D5/S3/Quantum/Petz/DoubleStieltjesRepresentations
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive product-space Stieltjes transforms of the simplex kernel and the symmetric logarithmic kernel. -/

import D5.S3.Quantum.Petz.DoubleStieltjesMarginals

namespace D5.S3.Quantum.Petz.DoubleStieltjesRepresentations

open Set MeasureTheory
open scoped Topology
open D5.S3.Quantum.PositiveResolvent.EulerResolvent
open D5.S3.Quantum.Petz.DoubleStieltjes
open D5.S3.Quantum.Petz.DoubleStieltjesMarginals

private lemma simplex_row_integral {x : ℝ} (hx : 0 < x) (y z : ℝ)
    {p : ℝ × ℝ} (hp : p ∈ triangle) :
    IntegrableOn (fun s => aMarginalIntegrand z s y p / (x+s)) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), aMarginalIntegrand z s y p / (x+s)) =
        Real.pi * qIntegrand x y z p := by
  have ha0 : 0 < p.1 := hp.1
  have ha1 : p.1 < 1 := by have := hp.2.1; have := hp.2.2; linarith
  let c := Real.pi *
    Real.exp (-p.2 * Real.log y + (p.1+p.2-1) * Real.log z)
  have heq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      aMarginalIntegrand z s y p / (x+s) =
        c * (Real.sin (Real.pi * p.1) / Real.pi * (s ^ (-p.1) / (x+s))) := by
    unfold aMarginalIntegrand
    rw [Real.rpow_def_of_pos hs]
    have hexp : -p.1 * Real.log s - p.2 * Real.log y +
        (p.1+p.2-1) * Real.log z =
        (-p.2 * Real.log y + (p.1+p.2-1) * Real.log z) + Real.log s * (-p.1) := by ring
    rw [hexp, Real.exp_add]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hi := ((euler_resolvent_integrable p.1 x ha0 ha1 hx).const_mul
    (Real.sin (Real.pi*p.1) / Real.pi)).const_mul c
  constructor
  · exact IntegrableOn.congr_fun hi (fun s hs => (heq s hs).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
      integral_const_mul, ← euler_resolvent p.1 x ha0 ha1 hx, Real.rpow_def_of_pos hx]
    unfold qIntegrand
    have hexp : -p.1 * Real.log x - p.2 * Real.log y +
        (p.1+p.2-1) * Real.log z =
        (-p.2 * Real.log y + (p.1+p.2-1) * Real.log z) + Real.log x * (-p.1) := by ring
    rw [hexp, Real.exp_add]
    dsimp [c]
    ring

private lemma simplex_marginal_transform {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    IntegrableOn (fun s =>
      (∫ p in triangle, aMarginalIntegrand z s y p ∂(volume.prod volume)) / (x+s)) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ),
      (∫ p in triangle, aMarginalIntegrand z s y p ∂(volume.prod volume)) / (x+s)) =
      Real.pi * ∫ p in triangle, qIntegrand x y z p ∂(volume.prod volume) := by
  let μ := (volume.prod volume).restrict triangle
  let ν := volume.restrict (Ioi (0 : ℝ))
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => aMarginalIntegrand z q.2 y q.1 / (x+q.2)
  have hf : Measurable f := by unfold f aMarginalIntegrand; fun_prop
  have hgcont : Continuous (qIntegrand x y z) := by unfold qIntegrand; fun_prop
  have hg : Integrable (fun p => Real.pi * qIntegrand x y z p) μ :=
    (((hgcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set triangle_subset).const_mul Real.pi)
  have hfin : Integrable f (μ.prod ν) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem triangle_isOpen.measurableSet] with p hp
      exact (simplex_row_integral hx y z hp).1
    · apply hg.congr
      filter_upwards [ae_restrict_mem triangle_isOpen.measurableSet] with p hp
      have he : (∫ s, ‖f (p,s)‖ ∂ν) = ∫ s, f (p,s) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        change 0 < s at hs
        change ‖aMarginalIntegrand z s y p / (x+s)‖ = aMarginalIntegrand z s y p / (x+s)
        apply Real.norm_of_nonneg
        apply div_nonneg _ (add_pos hx hs).le
        unfold aMarginalIntegrand
        apply mul_nonneg _ (Real.exp_pos _).le
        have ha1 : p.1 < 1 := by have := hp.2.1; have := hp.2.2; linarith
        exact (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp.1)
          (by simpa only [mul_one] using mul_lt_mul_of_pos_left ha1 Real.pi_pos)).le
      rw [he]
      exact (simplex_row_integral hx y z hp).2.symm
  have heq (s : ℝ) :
      (∫ p in triangle, aMarginalIntegrand z s y p ∂(volume.prod volume)) / (x+s) =
        ∫ p, f (p,s) ∂μ := by dsimp [f, μ]; rw [integral_div]
  constructor
  · exact hfin.integral_prod_right.congr (Filter.Eventually.of_forall fun s => (heq s).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall heq),
      ← integral_integral_swap (f := fun p s => f (p,s)) (μ := μ) (ν := ν) hfin]
    have hrow : (∫ p, ∫ s, f (p,s) ∂ν ∂μ) = ∫ p, Real.pi * qIntegrand x y z p ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem triangle_isOpen.measurableSet] with p hp
      exact (simplex_row_integral hx y z hp).2
    rw [hrow, integral_const_mul]

/-- Formula (8), with its finite product integral equal to the power-simplex integral. -/
theorem A_double_stieltjes {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℝ) :
    Integrable (fun p : ℝ × ℝ => A z p.1 p.2 / ((x+p.1)*(y+p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
    (∫ p, A z p.1 p.2 / ((x+p.1)*(y+p.2))
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) =
        ∫ p in triangle, qIntegrand x y z p ∂(volume.prod volume) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let f : ℝ × ℝ → ℝ := fun p => A z p.1 p.2 / ((x+p.1)*(y+p.2))
  have hfg (s t : ℝ) : f (s,t) = (A z s t / (y+t)) / (x+s) := by
    dsimp [f]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hrow (s : ℝ) : Integrable (fun t => f (s,t)) ν ∧
      (∫ t, f (s,t) ∂ν) = (1 / Real.pi) *
        ((∫ p in triangle, aMarginalIntegrand z s y p ∂(volume.prod volume)) / (x+s)) := by
    have h := A_marginal z s hy
    constructor
    · exact (h.1.div_const (x+s)).congr (Filter.Eventually.of_forall fun t => (hfg s t).symm)
    · rw [integral_congr_ae (Filter.Eventually.of_forall (hfg s)), integral_div, h.2]
      ring
  have hg := simplex_marginal_transform hx y z
  have hf : Measurable f := (A_measurable z).div (by fun_prop)
  have hfin : Integrable f (ν.prod ν) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun s => (hrow s).1
    · apply (hg.1.const_mul (1 / Real.pi)).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have he : (∫ t, ‖f (s,t)‖ ∂ν) = ∫ t, f (s,t) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 0 < s at hs
        change 0 < t at ht
        exact Real.norm_of_nonneg (div_nonneg (A_pos z s t).le
          (mul_pos (add_pos hx hs) (add_pos hy ht)).le)
      rw [he]
      exact (hrow s).2.symm
  refine ⟨hfin, ?_⟩
  rw [integral_prod f hfin]
  have he : (∫ s, ∫ t, f (s,t) ∂ν ∂ν) = (1 / Real.pi) *
      (∫ s in Ioi (0 : ℝ),
        (∫ p in triangle, aMarginalIntegrand z s y p ∂(volume.prod volume)) / (x+s)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => (hrow s).2)
  rw [he, hg.2]
  field_simp [Real.pi_ne_zero]

/-- Formula (8), identified with the canonical symmetric exponential second difference. -/
theorem Q_double_stieltjes {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℝ) :
    Integrable (fun p : ℝ × ℝ => A z p.1 p.2 / ((x+p.1)*(y+p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
    (∫ p, A z p.1 p.2 / ((x+p.1)*(y+p.2))
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) =
        D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference.Q x y z := by
  have h := A_double_stieltjes hx hy z
  exact ⟨h.1, h.2.trans (Q_eq_simplex x y z).symm⟩

end D5.S3.Quantum.Petz.DoubleStieltjesRepresentations
