/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: The actual reflected mass-zero finite Gaussian comparison at kappa=3/4. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedAll
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixActualJacobi
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixActualPayment
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixActualRatio
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4FinitePerturbation
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianInfiniteJacobi
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianActualNormBudget

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap475
open FiniteGaussianCap4
open FiniteGaussianCap4.LaguerreSevenHalf

/-- The actual matrix enclosure and original finite LDL certificate apply
to every actual head, including zero. No matrix-entry premise is retained. -/
theorem finiteGaussian_actual_head_certificate {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    0 ≤ rho * (∑ k ∈ Finset.range 16,
      (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site (2 * k)) ^ 2 -
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x *
        finiteGaussianPartialSum c site 32 x ^ 2) +
      (1 / 10 : ℝ) * jacobiPaidHead
        (fun k => finiteGaussianNormalizedCoefficient c site (2 * k)) -
      (23 / 20 : ℝ) *
        ∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2 := by
  have hsym : Matrix.IsSymm (compactMomentMatrix : Matrix (Fin 16) (Fin 16) ℝ) :=
    Matrix.IsSymm.ext (fun i j => compactMomentMatrix_symm j i)
  have hentry (i j : Fin 16) :
      |compactMomentMatrix i j - Cap4FiniteCertificate.center i j| ≤
        Cap4FinitePerturbation.delta := by
    simpa only [Cap4FinitePerturbation.delta] using (compactMomentMatrix_bounds i j).le
  have h := Cap4FinitePerturbation.perturbed_energy_nonneg
    compactMomentMatrix hsym hentry (actualCentralHeadCoordinates c site)
  have hrho : Cap4FinitePerturbation.rho = rho := by
    norm_num [Cap4FinitePerturbation.rho, Cap4FiniteCertificate.rhoQ, rho]
  dsimp only [Cap4FinitePerturbation.energy] at h
  rw [hrho,
    ← actual_head_charge_coordinates c site,
    ← finiteGaussianPrefix_compact_quadratic c site reflection hc hs,
    ← actual_jacobiPaidHead_coordinates c site,
    ← actual_head_norm_coordinates c site] at h
  exact h

/-- Complete physical coercivity for the same reflected finite real source
of zero total mass. Actual integrability, matrix enclosure, head/tail norms,
central charge, and the endpoint-retaining Jacobi payment are all consumed. -/
theorem finiteGaussian_cap475_coercivity {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i)
    (hmass : ∑ i, c i = 0) :
    (3 / 4 : ℝ) * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2) ≤
      ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2 := by
  have hquad := (finiteGaussian_capWeight_quadratic_lower c site).2
  have hpayment := finiteGaussian_compact_head_tail_payment c site
  have hboundary := finiteGaussian_actual_boundary_payment c site reflection hc hs
  have hhead := finiteGaussian_actual_head_norm c site reflection hc hs
  have hnorm := finiteGaussian_actual_head_tail_norm c site reflection hc hs
  have htail := finiteGaussian_actual_complete_tail_charge c site
  rw [finiteGaussian_actual_zero_tail_charge c site hmass, neg_sq,
    finiteGaussian_actual_tailH_budget c site reflection hc hs] at htail
  have hcertificate := finiteGaussian_actual_head_certificate c site reflection hc hs
  rw [hhead] at hpayment
  rw [hnorm]
  linarith [hquad, hpayment, hboundary, htail, hcertificate]

/-- The original strict physical ratio, for every globally nonzero source
with the same reflection symmetry and zero mass. No coercivity, entry bound,
integrability, expansion, or Parseval hypothesis is assumed. -/
theorem finiteGaussian_cap475_ratio {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i)
    (hmass : ∑ i, c i = 0) (hF : gaussianFeature c site ≠ 0) :
    (19 / 4 : ℝ) <
      (∫ x in Ioi Real.pi, x ^ 6 * gaussianFeature c site x ^ 2) /
        (Real.pi ^ 6 * (∫ x in Ioi Real.pi, gaussianFeature c site x ^ 2)) :=
  finiteGaussian_ratio_gt_nineteen_four_of_coercive c site hF
    (finiteGaussian_cap475_coercivity c site reflection hc hs hmass)

end FiniteGaussianCap475
