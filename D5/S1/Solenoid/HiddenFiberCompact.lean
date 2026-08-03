/- GID: D5/S1/Solenoid/HiddenFiberCompact
   generality: I
   mirror-B: D5/B/S1/Solenoid/HiddenFiberCompact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The hidden fiber is closed, compact, and sequentially compact coordinatewise. -/

import D5.S1.Dynamics.UniversalSolenoidCompact

namespace D5.S1.Solenoid

open Filter Topology
open D5.S1.Dynamics

/-- The hidden fiber consists of compatible solenoid phases whose visible
coordinate is zero. -/
abbrev HiddenFiber := {theta : UniversalSolenoid // UniversalSolenoid.projection theta = 0}

instance : FirstCountableTopology UniversalSolenoid :=
  TopologicalSpace.firstCountableTopology_induced UniversalSolenoid
    (ℕ+ → AddCircle (1 : ℝ)) Subtype.val

instance : FirstCountableTopology HiddenFiber :=
  TopologicalSpace.firstCountableTopology_induced HiddenFiber
    UniversalSolenoid Subtype.val

/-- Convergence in the hidden fiber is exactly convergence in every circle
coordinate of the compatible family. -/
theorem hiddenFiber_tendsto_iff_coordinatewise
    (u : ℕ → HiddenFiber) (x : HiddenFiber) :
    Tendsto u atTop (nhds x) ↔
      ∀ m : ℕ+, Tendsto (fun n => (u n).1.1 m) atTop (nhds (x.1.1 m)) := by
  rw [tendsto_subtype_rng]
  have hinducing :
      Topology.IsInducing
        (Subtype.val : UniversalSolenoid → (ℕ+ → AddCircle (1 : ℝ))) := ⟨rfl⟩
  rw [hinducing.tendsto_nhds_iff]
  simpa [Function.comp_def] using
    (tendsto_pi_nhds (Y := ℕ) (A := fun _ : ℕ+ => AddCircle (1 : ℝ))
      (f := fun n => (u n).1.1) (g := x.1.1) (u := atTop))

/-- The hidden fiber is closed, compact, and sequentially compact. The
sequential conclusion is the topological form of the diagonal argument:
successively stabilize coordinates and take the diagonal subsequence;
`hiddenFiber_tendsto_iff_coordinatewise` identifies its limit with
coordinatewise convergence, while compatibility passes to the limit. -/
theorem hiddenFiber_closed_compact_seqCompact :
    IsClosed {theta : UniversalSolenoid | UniversalSolenoid.projection theta = 0} ∧
    IsCompact (Set.univ : Set HiddenFiber) ∧
    IsSeqCompact (Set.univ : Set HiddenFiber) := by
  have hclosed :
      IsClosed {theta : UniversalSolenoid | UniversalSolenoid.projection theta = 0} :=
    isClosed_singleton.preimage UniversalSolenoid.continuous_projection
  have hcompact : IsCompact (Set.univ : Set HiddenFiber) := by
    exact isCompact_iff_isCompact_univ.mp hclosed.isCompact
  exact ⟨hclosed, hcompact, hcompact.isSeqCompact⟩

end D5.S1.Solenoid
