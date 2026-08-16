/- GID: D5/S3/QuantumChannels/BoundaryArtanhDivergence
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/BoundaryArtanhDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The mixed-state logarithmic tax diverges at the pure-state boundary. -/

import Mathlib.Analysis.SpecialFunctions.Artanh

open Filter Set Topology

namespace D5.S3.QuantumChannels.BoundaryArtanhDivergence

/-- The boundary coefficient `r * artanh r / 2` diverges as `r` approaches one from below. -/
theorem logarithmic_tax_diverges_at_boundary :
    Tendsto (fun r : ℝ => r * Real.artanh r / 2) (𝓝[<] 1) atTop := by
  have hArtanh : Tendsto Real.artanh (𝓝[<] (1 : ℝ)) atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [Ioo_mem_nhdsLT (Real.tanh_lt_one b)] with r hr
    rw [← Real.artanh_tanh b]
    exact (Real.artanh_lt_artanh (Real.neg_one_lt_tanh b) hr.2 hr.1).le
  have hHalf : Tendsto (fun r : ℝ => r / 2) (𝓝[<] (1 : ℝ)) (𝓝 ((1 : ℝ) / 2)) := by
    exact (tendsto_id.div_const 2).mono_left inf_le_left
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    hArtanh.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hHalf

end D5.S3.QuantumChannels.BoundaryArtanhDivergence
