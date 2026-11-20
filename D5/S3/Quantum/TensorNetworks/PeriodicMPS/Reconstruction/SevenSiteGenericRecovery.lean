/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGenericRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGenericRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: One adjacent two-site marginal identifies a generic actual seven-site projector against the compact closure. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphContinuation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphCriticalDimension

/-! Generic seven-site reconstruction from one adjacent two-site density. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteGenericRecovery

open Set Filter Function
open scoped Topology Matrix.Norms.Elementwise
open SevenSiteCompactGraph (chart)
open SevenSiteGraphReadout (ProjectorSource observe)
open SevenSiteGraphCriticalDimension
open SevenSiteGraphContinuation (exists_open_dense_actual_state_recovery)
open SevenSitePhysicalRankAssembly (graphReadout graphReadout_eqOn)
open PeriodicMPSUniformHardCoreLocalization (actualProjectors twoSiteObservation)

/-- On a relatively open dense subset of the compact seven-site state space,
a single adjacent two-site density identifies the full trace-word projector.
The identified state is actual, and competitors range over the compact closure. -/
theorem generic_twoSite_recovery :
    ∃ G : Set ProjectorSource, IsOpen G ∧ Dense G ∧ ∀ P ∈ G,
      P.val ∈ actualProjectors 5 ∧ ∀ Q : ProjectorSource,
        twoSiteObservation 5 Q.val = twoSiteObservation 5 P.val → Q = P := by
  refine exists_open_dense_actual_state_recovery isCompact_graphBadLocus
    dimH_graphBadLocus_le subset_union_left ?_
  intro u hu hGood
  have hRank := (not_mem_graphBadLocus_iff.mp hGood).2
  rw [chart.left_inv hu] at hRank
  have hEq : observe ∘ chart =ᶠ[𝓝 u] graphReadout :=
    Filter.mem_of_superset (chart.open_source.mem_nhds hu)
      fun v hv => (graphReadout_eqOn hv).symm
  rw [hEq.fderiv_eq (𝕜 := ℝ)]
  exact hRank

#print axioms generic_twoSite_recovery

end D5.S3.Quantum.TensorNetworks.SevenSiteGenericRecovery
