/- GID: D5/S3/Observer/Completion/InfiniteParityContinuityObstruction
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/InfiniteParityContinuityObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-support total parity has no continuous completion on all Boolean paths. -/

import D5.S3.Observer.ProbabilisticClosure.FiniteMarginalGlobalReadoutContrast

/- Library-search audit trail (2026-09-04):
   * Repository searches for finite-support parity, infinite parity, continuous
     completion, and dense finite configurations found no exact D5 theorem.
   * The frozen `FiniteMarginalGlobalReadoutContrast.readout` is the canonical
     map from a finite set of coordinates to its Boolean path and is reused here.
   * Pinned Mathlib provides `tendsto_pi_nhds`, discrete singleton neighborhoods,
     and the even/odd lemmas, but no theorem stating this parity obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.InfiniteParityContinuityObstruction

open Filter
open scoped Topology
open D5.S3.Observer.ProbabilisticClosure.FiniteMarginalGlobalReadoutContrast

/-- Total parity on finite Boolean configurations cannot be extended continuously
to the full countable product of Boolean coordinates. The natural-number index
enumerates the source's prime coordinates, while `readout support` is exactly the
configuration with that finite support. -/
theorem finite_support_parity_has_no_continuous_completion :
    ¬ ∃ extension : (Nat -> Bool) -> Bool,
      Continuous extension ∧
        ∀ support : Finset Nat,
          extension (readout support) = decide (Odd support.card) := by
  rintro ⟨extension, extensionContinuous, agreesOnFiniteSupport⟩
  let allActive : Nat -> Bool := fun _ => true
  have prefixTendsToAllActive :
      Tendsto (fun n : Nat => readout (Finset.range n)) atTop (𝓝 allActive) := by
    apply tendsto_pi_nhds.2
    intro i
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.Ici_mem_atTop (i + 1)] with n hn
    simp [readout, allActive, Finset.mem_range,
      Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hn]
  have parityTendsToExtension :
      Tendsto (fun n : Nat => extension (readout (Finset.range n))) atTop
        (𝓝 (extension allActive)) := by
    have atBoundary :
        Tendsto extension (𝓝 allActive) (𝓝 (extension allActive)) :=
      extensionContinuous.continuousAt
    exact atBoundary.comp prefixTendsToAllActive
  have parityEventuallyConstant :
      ∀ᶠ n : Nat in atTop,
        extension (readout (Finset.range n)) = extension allActive := by
    have singletonNeighborhood :
        ({extension allActive} : Set Bool) ∈ 𝓝 (extension allActive) := by
      simp
    filter_upwards [parityTendsToExtension.eventually singletonNeighborhood] with n hn
    exact Set.mem_singleton_iff.mp hn
  obtain ⟨threshold, afterThreshold⟩ :=
    Filter.eventually_atTop.mp parityEventuallyConstant
  have evenValue := afterThreshold (2 * threshold) (by omega)
  have oddValue := afterThreshold (2 * threshold + 1) (by omega)
  rw [agreesOnFiniteSupport] at evenValue oddValue
  have impossible :
      decide (Odd (Finset.range (2 * threshold)).card) =
        decide (Odd (Finset.range (2 * threshold + 1)).card) :=
    evenValue.trans oddValue.symm
  have evenParity : ¬ Odd (2 * threshold) :=
    Nat.not_odd_iff_even.mpr (even_two_mul threshold)
  have oddParity : Odd (2 * threshold + 1) :=
    odd_two_mul_add_one threshold
  simp [Finset.card_range, evenParity, oddParity] at impossible

-- The completed path space and the proposed continuous-map carrier are inhabited.
example : Nonempty (Nat -> Bool) := ⟨fun _ => false⟩

example : Continuous (fun _ : Nat -> Bool => false) := continuous_const

#print axioms finite_support_parity_has_no_continuous_completion

end D5.S3.Observer.Completion.InfiniteParityContinuityObstruction
