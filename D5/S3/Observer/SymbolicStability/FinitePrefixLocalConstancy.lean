/- GID: D5/S3/Observer/SymbolicStability/FinitePrefixLocalConstancy
   generality: G
   mirror-B: D5/B/S3/Observer/SymbolicStability/FinitePrefixLocalConstancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite symbolic prefix is locally constant off its boundary union. -/

import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/- Library-search audit trail (2026-08-16):
   * Repository and digestion-record searches found no equivalent D5 declaration.
   * Local smart-search and pinned-Mathlib source searches found no complete theorem
     matching the finite-prefix common-radius conclusion.
   * The exact support hits `Filter.eventually_all` and
     `Metric.eventually_nhds_iff` are imported and applied below.
   * `LocallyConstant.unflip` is a related stronger, global construction. -/

namespace D5.S3.Observer.SymbolicStability.FinitePrefixLocalConstancy

/-- If each symbol is locally constant away from its boundary and a point avoids
the union of the first `N` boundaries, the entire finite prefix is constant on
one common metric neighborhood of that point. -/
theorem finite_prefix_locally_constant_off_boundary
    {X A : Type*} [PseudoMetricSpace X] {N : Nat}
    (w : Fin N -> X -> A) (boundary : Fin N -> Set X)
    (hlocal : forall n theta, theta ∉ boundary n ->
      ∀ᶠ theta' in nhds theta, w n theta' = w n theta)
    (theta : X) (houtside : theta ∉ ⋃ n, boundary n) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ theta', dist theta' theta < epsilon -> ∀ n, w n theta' = w n theta := by
  have hall : ∀ᶠ theta' in nhds theta, ∀ n, w n theta' = w n theta := by
    rw [Filter.eventually_all]
    intro n
    apply hlocal n theta
    intro hboundary
    exact houtside (Set.mem_iUnion.mpr ⟨n, hboundary⟩)
  exact Metric.eventually_nhds_iff.mp hall

end D5.S3.Observer.SymbolicStability.FinitePrefixLocalConstancy
