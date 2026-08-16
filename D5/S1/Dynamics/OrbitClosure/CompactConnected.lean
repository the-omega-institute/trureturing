/- GID: D5/S1/Dynamics/OrbitClosure/CompactConnected
   generality: G
   mirror-B: D5/B/S1/Dynamics/OrbitClosure/CompactConnected
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous real-orbit closures in compact metric spaces are compact and connected. -/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Basic

namespace D5.S1.Dynamics.OrbitClosure.CompactConnected

open Set

/- Pinned Mathlib supplies `isConnected_range`, `IsConnected.closure`, and
   `IsClosed.isCompact`; no single declaration combines the two conclusions. -/

/-- The closure of a continuous real-parameter orbit in a compact metric space is
both compact and connected. -/
theorem orbit_closure_is_compact_and_connected
    {W : Type*} [MetricSpace W] [CompactSpace W]
    (flow : ℝ × W → W) (hflow : Continuous flow) (xi0 : W) :
    IsCompact (closure (Set.range fun t : ℝ ↦ flow (t, xi0))) ∧
      IsConnected (closure (Set.range fun t : ℝ ↦ flow (t, xi0))) := by
  constructor
  · exact isClosed_closure.isCompact
  · exact
      (isConnected_range
        (hflow.comp (continuous_id.prodMk continuous_const))).closure

#print axioms orbit_closure_is_compact_and_connected

end D5.S1.Dynamics.OrbitClosure.CompactConnected
