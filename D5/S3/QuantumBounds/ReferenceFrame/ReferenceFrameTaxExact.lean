/- GID: D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Package the finite exchange-channel fidelity, sharp tax, flat tax, and paired top space. -/

import D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
import D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace

namespace D5.S3.QuantumBounds.ReferenceFrame.ReferenceFrameTaxExact

open scoped BigOperators
open scoped Matrix
open D5.S3.QuantumBounds.ReferenceFrameTax
open D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
open D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace

/-!
The finite channel statement is kept at the concrete exchange model already defined in the
imported bridge. The flat identity carries its necessary `2 <= N` restriction; the frozen
one-level calculation records why that restriction cannot be removed.
-/

theorem reference_frame_tax_exact (N : ℕ) (hN : 2 ≤ N) :
    (exchangeUnitary N)ᴴ * exchangeUnitary N = 1 ∧
    (∀ x : JointBasis N, totalExcitation (exchangeBasis x) = totalExcitation x) ∧
    (∀ (c : Fin N → ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ),
      exchangeChannel c rho =
        ∑ r : Fin N, exchangeKraus c r * rho * (exchangeKraus c r)ᴴ) ∧
    (∀ c : Fin N → ℝ, entanglementFidelity c = nearestNeighborQuadratic c) ∧
    (∀ c : Fin N → ℝ,
      entanglementFidelity c =
        ∑ r : Fin N,
          (((if _h : 0 < r.val then
              c ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩ else 0) +
            (if _h : r.val + 1 < N then c ⟨r.val + 1, _h⟩ else 0)) / 2) ^ 2) ∧
    IsGreatest
      {q : ℝ | ∃ c : Fin N → ℝ, (∑ i, c i ^ 2) = 1 ∧ entanglementFidelity c = q}
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2) ∧
    1 - Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 =
      Real.sin (Real.pi / (N + 1 : ℝ)) ^ 2 ∧
    1 - nearestNeighborQuadratic (N := N) (fun _ => 1 / Real.sqrt (N : ℝ)) =
      3 / (2 * (N : ℝ)) ∧
    squaredTopEigenspace N = topModeSpace N ∧
    Module.finrank ℝ (squaredTopEigenspace N) = 2 := by
  have hgreat :
      IsGreatest
        {q : ℝ | ∃ c : Fin N → ℝ, (∑ i, c i ^ 2) = 1 ∧
          nearestNeighborQuadratic c = q}
        (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2) :=
    reference_frame_tax_isGreatest N (by omega)
  have hchannel :
      IsGreatest
        {q : ℝ | ∃ c : Fin N → ℝ, (∑ i, c i ^ 2) = 1 ∧ entanglementFidelity c = q}
        (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2) := by
    constructor
    · rcases hgreat.1 with ⟨c, hc, hq⟩
      exact ⟨c, hc, by rw [entanglement_fidelity_eq_nearest_neighbor_quadratic c, hq]⟩
    · intro q hq
      rcases hq with ⟨c, hc, hq⟩
      apply hgreat.2
      exact ⟨c, hc, by rw [← entanglement_fidelity_eq_nearest_neighbor_quadratic c, hq]⟩
  refine ⟨exchange_unitary_is_unitary N, exchange_basis_preserves_total_excitation,
    ?_, ?_, ?_, hchannel, reference_frame_tax_optimal_identity N (by omega),
    flat_reference_frame_tax N hN, squared_top_eigenspace_eq_top_mode_space N hN,
    squared_top_eigenspace_finrank N hN⟩
  · intro c rho
    exact exchange_channel_kraus_form c rho
  · intro c
    exact entanglement_fidelity_eq_nearest_neighbor_quadratic c
  · intro c
    exact entanglement_fidelity_eq_average_norm_sq c

#print axioms reference_frame_tax_exact

end D5.S3.QuantumBounds.ReferenceFrame.ReferenceFrameTaxExact
