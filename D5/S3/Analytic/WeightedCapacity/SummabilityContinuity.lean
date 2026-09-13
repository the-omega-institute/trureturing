/- GID: D5/S3/Analytic/WeightedCapacity/SummabilityContinuity
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/SummabilityContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity of finite-support dyadic readout at zero forces finite total capacity. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Constructions
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.SummabilityContinuity

open Set Filter
open scoped Topology BigOperators
open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

/-- Continuity of the finite-support dyadic readout at zero excludes divergent capacity. -/
theorem continuousAt_readout_zero_implies_M_ne_top (A : ℕ → ℕ)
    (hcont : ContinuousAt (@readout A) ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩, by simp⟩) :
    M A ≠ ⊤ := by
  sorry

#print axioms continuousAt_readout_zero_implies_M_ne_top

end D5.S3.Analytic.WeightedCapacity.SummabilityContinuity
