/- GID: D5/S1/Solenoid/RealFlowNonDiscrete
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorial recurrence makes the faithful real-flow range non-discrete at zero. -/

import Mathlib
import D5.S1.Solenoid.RealFlowRecurrence

/- Provenance: Native proof over pinned mathlib. -/

/- Library-search audit trail (2026-08-16):
   * No one-step lemma turning a convergent point-avoiding sequence into an
     `AccPt` of its range was found.
   * `Filter.Tendsto.mapClusterPt`, `accPt_iff_clusterPt`, and
     `ClusterPt.mono` supply the filter-level accumulation argument.
   * `nhds_ne_subtype_neBot_iff` and `discreteTopology_iff_nhds_ne` identify
     the induced topology on the range subtype and obstruct discreteness.
-/

namespace D5.S1.Solenoid.RealFlowNonDiscrete

open Filter Topology
open D5.S1.Dynamics

/-- Every factorial time has a nonzero image under the faithful real flow. -/
theorem realFlow_factorial_ne_zero (n : ℕ) :
    UniversalSolenoid.realFlow (Nat.factorial n : ℝ) ≠ 0 := by
  intro hflow
  have hfactorial : (Nat.factorial n : ℝ) = 0 :=
    (RealFlowInjectivity.realFlow_eq_zero_iff _).1 hflow
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) hfactorial

/-- Zero is an accumulation point of the range of the universal-solenoid real flow. -/
theorem realFlow_range_accPt_zero :
    AccPt (0 : UniversalSolenoid)
      (Filter.principal (Set.range UniversalSolenoid.realFlow)) := by
  let u : ℕ → UniversalSolenoid := fun n =>
    UniversalSolenoid.realFlow (Nat.factorial n : ℝ)
  have hu : Tendsto u atTop (nhds 0) :=
    RealFlowRecurrence.realFlow_factorial_tendsto_zero
  rw [accPt_iff_clusterPt]
  apply hu.mapClusterPt.clusterPt.mono
  refine le_inf ?_ ?_
  · rw [Filter.le_principal_iff]
    change ∀ᶠ n : ℕ in atTop, u n ∈ ({0} : Set UniversalSolenoid)ᶜ
    exact Filter.Eventually.of_forall fun n => by
      simpa [u] using realFlow_factorial_ne_zero n
  · rw [Filter.le_principal_iff]
    change ∀ᶠ n : ℕ in atTop, u n ∈ Set.range UniversalSolenoid.realFlow
    exact Filter.Eventually.of_forall fun n =>
      ⟨(Nat.factorial n : ℝ), by simp only [u]⟩

/-- The real-flow image is not discrete in its induced subtype topology. -/
theorem realFlow_range_not_discreteTopology :
    ¬ DiscreteTopology (Set.range UniversalSolenoid.realFlow) := by
  intro hdiscrete
  let zeroInRange : Set.range UniversalSolenoid.realFlow :=
    ⟨0, ⟨0, UniversalSolenoid.realFlow_zero⟩⟩
  have hpunctured : (𝓝[≠] zeroInRange).NeBot :=
    nhds_ne_subtype_neBot_iff.mpr (by
      simpa only [zeroInRange, AccPt] using realFlow_range_accPt_zero)
  exact hpunctured.ne ((discreteTopology_iff_nhds_ne.mp hdiscrete) zeroInRange)

#print axioms realFlow_factorial_ne_zero
#print axioms realFlow_range_accPt_zero
#print axioms realFlow_range_not_discreteTopology

end D5.S1.Solenoid.RealFlowNonDiscrete
