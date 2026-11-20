import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.CompactRegularFiberContinuation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformHardCoreCompactRecovery
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout

set_option autoImplicit false

open Set Filter Function
open scoped Topology ENNReal NNReal Matrix.Norms.Elementwise

namespace D5.S3.Quantum.TensorNetworks

open PeriodicMPSRegularComplement PeriodicMPSCompactAnalyticCharts
open PeriodicMPSUniformHardCoreLocalization
open PeriodicMPSCompactReadout (Readout readout readout_eq_iff)

private abbrev CompactProjectors (r : ℕ) := closure (actualProjectors (r + 2))
private abbrev Coord := Fin 8 → ℝ

/-- Continuation with the literal partial trace on the compact actual source.
The nine Pauli readouts are fixed and induce its exact fibers. At seven sites, take `r = 3`. -/
theorem compact_projector_application (r : ℕ) (hr : 3 ≤ r)
    {U B : Set (CompactProjectors r)} (hUo : IsOpen U) (hUc : IsConnected U) (hUd : Dense U)
    (hcover : Bᶜ ⊆ U) (hBc : IsCompact B) (hB : dimH B ≤ 6)
    (hcharts : ∀ x ∈ U, ∃ (c : OpenPartialHomeomorph Coord (CompactProjectors r))
        (K : ℝ≥0) (g : Coord → Readout),
      x ∈ c.target ∧ LipschitzOnWith K c.symm c.target ∧
        EqOn g ((fun p : CompactProjectors r => readout (twoSiteObservation (r + 2) p.val)) ∘ c)
          c.source ∧
        ∀ z ∈ c.source, c z ∉ B → AnalyticAt ℝ g z ∧ Injective (fderiv ℝ g z)) :
    ∃ D : Set (CompactProjectors r), IsOpen D ∧ Dense D ∧
      ∀ x ∈ D, ∀ y : CompactProjectors r,
        twoSiteObservation (r + 2) y.val = twoSiteObservation (r + 2) x.val → y = x := by
  let compactProjectors : CompactSpace (CompactProjectors r) :=
    isCompact_iff_compactSpace.mp (isCompact_closure_actualProjectors (r + 2))
  let f (p : CompactProjectors r) := readout (twoSiteObservation (r + 2) p.val)
  let Q := (twoSiteObservation (r + 2)).toContinuousLinearMap
  have hlip : LipschitzWith _ f := readout.lipschitzWith.comp (Q.lipschitzWith.comp isometry_subtype_coe.lipschitzWith)
  have hE : Module.finrank ℝ Coord = 8 := by simp [Coord]
  have hY : Module.finrank ℝ Readout = Module.finrank ℝ Coord + 1 := by simp [Readout, hE]
  have hd : 2 ≤ Module.finrank ℝ Coord := by simp [hE]
  have hb : dimH B ≤ ((Module.finrank ℝ Coord - 2 : ℕ) : ℝ≥0∞) := by simpa [hE] using hB
  have hs (hG : Dense (f ⁻¹' (f '' B)ᶜ)) :
      ∃ x ∈ f ⁻¹' (f '' B)ᶜ, ∀ y : CompactProjectors r, f y = f x → y = x := by
    obtain ⟨x, _, hx, hsingle⟩ :=
      PeriodicMPSUniformHardCoreCompactRecovery.exists_compact_singleton_mem_dense r hr hG
        (V := univ) univ_mem
    exact ⟨x, hx, fun y h => hsingle y ((readout_eq_iff x y).mp h)⟩
  obtain ⟨ho, hD⟩ := @compact_generic_recovery_of_dimH_bad Coord Readout
    _ _ _ _ _ _ (CompactProjectors r) _ compactProjectors f _ hlip
    U B hUo hUc hUd hcover hBc hd hb hY hcharts hs
  exact ⟨_, ho, hD, fun x hx y hy => hx.2 y ((readout_eq_iff x y).mpr hy)⟩

#print axioms PeriodicMPSCompactReadout.twoSiteObservation_mem_of_mem_closure
#print axioms PeriodicMPSCompactReadout.readout_eq_iff
#print axioms compact_projector_application

end D5.S3.Quantum.TensorNetworks
