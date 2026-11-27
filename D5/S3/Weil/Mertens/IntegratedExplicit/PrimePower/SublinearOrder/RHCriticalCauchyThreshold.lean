/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalCauchyThreshold
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalCauchyThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Cauchy energy cap ensures the Gaussian zeta collision limit at critical resolution. -/

import D5.S3.Analytic.Oscillation.MontgomeryCauchyDeficit
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalPairSumThreshold

/-! The critical harmonic collision limit under a positive Cauchy threshold. -/
open Filter
open scoped Topology
open D5.S3.Analytic.Oscillation.MontgomeryWindow (montgomery)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum zetaSpectrum_countAsymptotic)
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (ordinate)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
open D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit (pairMoment)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FejerCollisionVariance
open D5.S3.Fourier.Concentration.FejerCollisionLimit
open D5.S3.Analytic.Oscillation.MontgomeryCauchyDeficit

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalCauchyThreshold

open RHCriticalPairSumThreshold

/-- A Montgomery cap below the Cauchy alignment threshold suffices for the critical limit. -/
theorem harmonic_zeta_critical_collision_limit_of_cauchy_cap (rh : RiemannHypothesis)
    {κ : ℝ} (hκmax : κ < 2 * Real.pi * (1 / (2 * Real.pi)) ^ 2)
    (hcorr : ∀ A > (1 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        Y * Real.log Y / (2 * Real.pi) * montgomery (zetaSpectrum rh) (t / Real.log Y) Y ≤
          κ * Y * (Real.log Y) ^ 2)
    (T η : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hresolution : ∃ a > (0 : ℝ), ∀ᶠ n in atTop, a ≤ η n * Real.log (T n)) :
    let scale (n : ℕ) := Real.sqrt ((n : ℝ) * pairMoment
      (fun j : ↥(positiveCutoff rh (T n)) => ordinate j.1)
      (fun j => harmonicWeight j.1 / harmonicMass rh (T n)) 2 / 2)
    Tendsto (fun n : ℕ => η n / scale n) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => scale n *
      tailCollisionMass (fun j : ↥(positiveCutoff rh (T n)) => ordinate j.1)
        (fun j => harmonicWeight j.1) n (η n) /
        (η n * harmonicMass rh (T n)^(2*n))) atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
  have hη : ∀ᶠ n : ℕ in atTop, 0 < η n := by
    obtain ⟨a, ha, hprod⟩ := hresolution
    filter_upwards [hprod, hT.eventually_gt_atTop 1] with n hlower hheight
    exact pos_of_mul_pos_left (ha.trans_le hlower) (Real.log_pos hheight).le
  obtain ⟨d, hd, hlong⟩ := harmonic_long_deficit_of_cutoff_deficit rh
    (fractional_deficit_of_cauchy_cap _ (zetaSpectrum_countAsymptotic rh) hκmax hcorr)
  exact harmonic_zeta_critical_collision_limit_of_long_deficit rh
    (fun A hA => ⟨d, hd, hlong A hA⟩)
    T η hT hη hh hresolution

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalCauchyThreshold
