/- GID: D5/S3/Weil/TestFunctions/LaguerreLiBridge
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/LaguerreLiBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Specialize Cayley moment tomography to the natural half-scale Li curvature. -/

import D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

/- Library-search audit trail (2026-08-29):
   * D5 searches for a Laguerre--Li bridge and a canonical Li coefficient sequence
     found no exact owner.
   * `CayleyLaguerreMomentTomography.laguerre_moment_tomography` is the exact
     general-scale analytic owner specialized below; its Cayley moment and
     correlation primitives are imported rather than restated.
   * Pinned Mathlib searches for Laguerre polynomials and Laguerre moment
     identities found no hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Analytic.LiCausalTrichotomy
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

namespace D5.S3.Weil.TestFunctions.LaguerreLiBridge

/-- If the natural half-scale Cayley moments are the discrete curvatures of
the supplied Li sequence and their total mass is twice its first coefficient,
then every positive curvature is the stated Laguerre coefficient of the
real resolvent correlation. -/
theorem laguerre_li_bridge
    (rho : Measure Real) [IsFiniteMeasure rho]
    (hEven : Measure.map (fun xi : Real => -xi) rho = rho)
    (liCoefficient : Nat -> Real)
    (massIdentity : spectralMass rho = 2 * liCoefficient 1)
    (momentIdentity : forall n, 1 <= n ->
      (cayleyMoment rho n (1 / 2 : Real)).re =
        liCoefficient (n + 1) - 2 * liCoefficient n + liCoefficient (n - 1)) :
    forall n, 1 <= n ->
      liCoefficient (n + 1) - 2 * liCoefficient n + liCoefficient (n - 1) =
        2 * liCoefficient 1 -
          ∫ t : Real in Ioi 0,
            Real.exp (-t / 2) * laguerreOne (n - 1) t *
              (resolventCorrelation rho t).re := by
  intro n hn
  let kernel : Real -> Complex := fun t =>
    (Real.exp (-t / 2) * laguerreOne (n - 1) t : Real)
  let integrand : Real -> Complex := fun t =>
    kernel t * resolventCorrelation rho t
  have kernelIntegrable : IntegrableOn kernel (Ioi 0) := by
    have packetIntegrable := (causalPacket_isCausal n).1
    have reflectedIntegrable :
        Integrable (fun t : Real => causalPacket n (-t)) := by
      change Integrable (causalPacket n ∘ Neg.neg)
      exact (Measure.measurePreserving_neg volume).integrable_comp_of_integrable
        packetIntegrable
    apply reflectedIntegrable.integrableOn.neg.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hn0 : Not (n = 0) := Nat.ne_of_gt hn
    have ht0 : 0 < t := mem_Ioi.mp ht
    change -(causalPacket n (-t)) = kernel t
    simp only [kernel, causalPacket, hn0, if_false,
      neg_lt_zero.mpr ht0, if_true, neg_neg]
    push_cast
    ring
  have correlationStronglyMeasurable :
      StronglyMeasurable (resolventCorrelation rho) := by
    rw [show resolventCorrelation rho = fun t : Real =>
      ∫ xi : Real, Complex.exp (Complex.I * t * xi) ∂rho by rfl]
    exact (by fun_prop : StronglyMeasurable (fun z : Real × Real =>
      Complex.exp (Complex.I * z.1 * z.2))).integral_prod_right'
  have correlationBound (t : Real) :
      norm (resolventCorrelation rho t) <= spectralMass rho := by
    rw [resolventCorrelation, spectralMass]
    simpa using (norm_integral_le_of_norm_le_const (μ := rho) (C := 1)
      (Filter.Eventually.of_forall fun xi => by
        simp [Complex.norm_exp, Complex.mul_re]))
  have massNonnegative : 0 <= spectralMass rho := by
    simp [spectralMass]
  have integrandIntegrable : IntegrableOn integrand (Ioi 0) := by
    have dominating := kernelIntegrable.norm.const_mul (spectralMass rho)
    refine dominating.mono' ?_ ?_
    · exact kernelIntegrable.aestronglyMeasurable.mul
        correlationStronglyMeasurable.aestronglyMeasurable
    · filter_upwards with t
      rw [norm_mul]
      have hbound := correlationBound t
      simpa only [integrand, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg massNonnegative, mul_comm] using
          mul_le_mul_of_nonneg_left hbound (norm_nonneg (kernel t))
  have integralRealPart :
      (∫ t : Real in Ioi 0, integrand t).re =
        ∫ t : Real in Ioi 0,
          Real.exp (-t / 2) * laguerreOne (n - 1) t *
            (resolventCorrelation rho t).re := by
    calc
      (∫ t : Real in Ioi 0, integrand t).re =
          ∫ t : Real in Ioi 0, (integrand t).re := by
        simpa only [RCLike.re_eq_complex_re] using
          (integral_re integrandIntegrable).symm
      _ = ∫ t : Real in Ioi 0,
          Real.exp (-t / 2) * laguerreOne (n - 1) t *
            (resolventCorrelation rho t).re := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [integrand, kernel, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
  have tomography :=
    (laguerre_moment_tomography rho hEven hn
      (by norm_num : 0 < (1 / 2 : Real))).2
  norm_num [div_eq_mul_inv] at tomography
  have integrandEquality :
      (fun t : Real => Complex.exp (-(1 / 2 * (t : Complex))) *
        (laguerreOne (n - 1) t : Complex) * resolventCorrelation rho t) =
          integrand := by
    funext t
    simp only [integrand, kernel, Complex.ofReal_mul]
    rw [Complex.ofReal_exp]
    congr 3
    push_cast
    ring
  rw [integrandEquality] at tomography
  have realTomography := congrArg Complex.re tomography
  rw [momentIdentity n hn, massIdentity] at realTomography
  norm_num [integralRealPart] at realTomography
  simpa only [one_div, neg_mul, div_eq_mul_inv] using realTomography

#print axioms laguerre_li_bridge

end D5.S3.Weil.TestFunctions.LaguerreLiBridge
