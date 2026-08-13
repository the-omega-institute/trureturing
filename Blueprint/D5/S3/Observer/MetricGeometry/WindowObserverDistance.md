# Finite-Window Observer Distance and LP Doubling Cost

## Abstract

Finite cyclic distances are exact, and the local LP doubling cost has exact unbounded one-third growth.

**Theorem 1.1 (Finite-window observer distance equals cyclic distance).**

$$\forall M \in \mathbb{N}_{>0},\ \forall a, b \in \mathbb{Z}/M\mathbb{Z},\ d_{W}(a, b) = \operatorname{cyclicDist}(a, b).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_observer_distance_eq_cycle_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admissible observables are real functions on the finite cyclic window whose frozen ObserverMetric perturbation seminorm for the one-step cyclic update is at most one. A finite telescoping argument proves that this updateDefect-constrained ball equals the all-pairs cyclic-Lipschitz ball: each directed arc bounds an endpoint gap, and taking the shorter arc gives the cyclic metric. The distance-from-a observable belongs to that frozen ball through the bridge and attains the cyclic distance; the bridge gives the reverse bound. This is the atom's same-orbit finite-window clause only.

**Theorem 1.2 (A twelve-window antipode attains distance six).**

$$\exists f \in B_{W},\ f(0)\neq f(6) \land \Vert f(0)- f(6)\Vert = 6.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_twelve_antipode_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the twelve-point cyclic window, the clipped distance observable based at zero is admissible, is nonconstant at the antipode six, and realizes gap six. This supplies a concrete non-vacuity witness for the supremum.

**Theorem 1.3 (The twelve-window wrap gap is one).**

$$\operatorname{cyclicDist}(0, 11) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_wrap_unit_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoints zero and eleven are adjacent after cyclic wrap-around. Their distance is one rather than eleven, checking that the finite-window construction is genuinely cyclic.

**Theorem 1.4 (LP cost at a power-of-two window has the exact one-third formula).**

$$\forall m \in \mathbb{N},\ C_{2^{m}}(-\frac{1}{3}) = \frac{2^{m} - 1}{3}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lp_window_cost_power_two_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No frozen c_n family or corresponding cost function exists in the observer metric modules. Accordingly C_n(x) here is the self-contained cost of the n-1 adjacent steps in a nonempty n-window, each priced at -x. Its doubling law is C_(2n)(x) = 2 C_n(x) - x. At x = -1/3, induction on m and that doubling law give the displayed identity exactly.

This theorem formalizes the arithmetic core of the certificate footnote. It does not identify the local recurrence with an absent external c_n definition and does not assert that the external eight LP pairs all hit; those pair data were not supplied and are not reconstructed here.

**Theorem 1.5 (LP power-of-two costs are unbounded).**

$$\forall B \in \mathbb{R},\ \exists m \in \mathbb{N},\ B < \frac{2^{m} - 1}{3}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lp_window_cost_power_two_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real threshold B, Archimedean unboundedness of powers of two gives an exponent m with 2^m greater than 3B+1. Substitution into the exact formula proves that the corresponding local LP cost exceeds B.

**Theorem 1.6 (The four-window LP cost is one).**

$$C_{4}(-\frac{1}{3}) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lp_window_cost_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the recurrence at m = 2 gives C at four of -1/3 equal to one. This concrete positive value is the anti-vacuity check for the exact doubling formula.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lp_window_cost_four`
- Truth anchor: `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lp_window_cost_power_two_exact`
- Truth anchor: `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lp_window_cost_power_two_unbounded`
- Truth anchor: `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_observer_distance_eq_cycle_distance`
- Truth anchor: `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_twelve_antipode_witness`
- Truth anchor: `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_wrap_unit_check`
- Dependency: [D5/S3/Observer/ObserverMetric](../ObserverMetric.md)
