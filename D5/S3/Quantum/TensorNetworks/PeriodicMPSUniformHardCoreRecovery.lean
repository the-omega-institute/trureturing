/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLeadingCertificate, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticSeparation]
   utility: none
   digest: At every length at least seven, one adjacent marginal determines a relatively open dense set of targets near the hard-core witness against every actual periodic bond-two competitor. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLeadingCertificate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticSeparation

/-! Reconstruction from one adjacent pair near the cyclic independent-set state. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreRecovery

open PeriodicMPSUniformHardCoreAnalyticPartner
  (chart imagDirection exists_opposite_curve)
open PeriodicMPSUniformHardCoreAnalyticSeparation
  (reference_coordinates hasParityTaylor_of_fourth_order
    exists_generic_actual_reconstruction_of_matched_taylor)
open PeriodicMPSUniformHardCoreFoldCurvature (nullSlope)
open PeriodicMPSUniformHardCoreNormalizedJet (coordinates)
open PeriodicMPSUniformHardCoreLocalization

private theorem reference_eq_chart (n : ℕ) (ε : ℝ) :
    coordinates n PeriodicMPSUniformHardCoreJetElimination.original ε =
      chart ε (PeriodicMPSUniformHardCoreAnalyticPartner.original (nullSlope n)) := by
  rw [reference_coordinates]
  funext i
  fin_cases i <;>
    simp [chart, imagDirection, PeriodicMPSUniformHardCoreAnalyticPartner.original,
      PeriodicMPSUniformHardCoreFirstJet.witness]

/-- For every length at least seven, an open neighborhood of the equal-weight
independent-set state contains an open dense set of states determined by one
adjacent pair among all actual periodic binary bond-two states. -/
theorem exists_generic_actual_reconstruction (r : ℕ) (hr : 3 ≤ r) :
    ∃ N : Set (actualProjectors (r + 2)), IsOpen N ∧
      (⟨witnessProjector (r + 2), witnessProjector_mem_actualProjectors (by omega)⟩ :
        actualProjectors (r + 2)) ∈ N ∧
      ∃ G : Set N, IsOpen G ∧ Dense G ∧
        ∀ P ∈ G, ∀ Q : actualProjectors (r + 2),
          twoSiteObservation (r + 2) Q.val = twoSiteObservation (r + 2) P.val.val →
          Q.val = P.val.val := by
  have h := exists_opposite_curve (r + 4) (by omega)
  simp only [Nat.add_sub_cancel] at h
  obtain ⟨w, w₂, hw₀, hw, he, hz, hx, hd, hd', hEq, hne, ht⟩ := h
  apply exists_generic_actual_reconstruction_of_matched_taylor r hr
    (hasParityTaylor_of_fourth_order ht)
  · rfl
  · simpa only [← reference_eq_chart] using hEq

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreRecovery
