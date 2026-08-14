/- GID: D5/S3/Zeros/Endpoints/XiProductEndpointLimits
   generality: I
   mirror-B: D5/B/S3/Zeros/Endpoints/XiProductEndpointLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The displayed xi product form attains both endpoint values through punctured limits. -/

import D5.S3.Analytic.CompletedZetaMellinReconstruction
import D5.S3.Zeros.Endpoints.XiEndpointValues

namespace D5.S3.Zeros.Endpoints.XiProductEndpointLimits

open Filter Topology
open scoped Topology
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues

/-- The displayed xi product tends to one-half as `s` approaches zero away from zero. -/
theorem xi_product_form_tendsto_zero :
    Tendsto (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedZetaReading s)
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 2 : ℂ)) := by
  have hReconstruction :=
    D5.S3.Analytic.CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction
  have hPole := hReconstruction.2.2.2.2.2.1.1
  have hFactor :
      Tendsto (fun s : ℂ => (1 / 2 : ℂ) * (s - 1)) (𝓝[≠] (0 : ℂ))
        (𝓝 ((1 / 2 : ℂ) * (0 - 1))) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (tendsto_const_nhds.mul (tendsto_id.sub tendsto_const_nhds))
  convert hFactor.mul hPole using 1 <;> ring_nf

/-- The displayed xi product tends to one-half as `s` approaches one away from one. -/
theorem xi_product_form_tendsto_one :
    Tendsto (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedZetaReading s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (1 / 2 : ℂ)) := by
  have hReconstruction :=
    D5.S3.Analytic.CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction
  have hPole := hReconstruction.2.2.2.2.2.1.2
  have hFactor :
      Tendsto (fun s : ℂ => (1 / 2 : ℂ) * s) (𝓝[≠] (1 : ℂ))
        (𝓝 ((1 / 2 : ℂ) * 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.mul tendsto_id)
  convert hFactor.mul hPole using 1 <;> ring_nf

/-- Both punctured product limits agree with the frozen endpoint values of `xiReading`. -/
theorem xi_product_form_attains_endpoint_values :
    (Tendsto (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedZetaReading s)
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 2 : ℂ)) ∧
      Tendsto (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedZetaReading s)
        (𝓝[≠] (1 : ℂ)) (𝓝 (1 / 2 : ℂ))) ∧
    (xiReading 0 = (1 / 2 : ℂ) ∧ xiReading 1 = (1 / 2 : ℂ)) := by
  exact
    ⟨⟨xi_product_form_tendsto_zero, xi_product_form_tendsto_one⟩,
      xi_reading_endpoint_values⟩

example : Nonempty ℂ := ⟨0⟩
example : NeBot (𝓝[≠] (0 : ℂ)) := inferInstance
example : NeBot (𝓝[≠] (1 : ℂ)) := inferInstance

end D5.S3.Zeros.Endpoints.XiProductEndpointLimits
