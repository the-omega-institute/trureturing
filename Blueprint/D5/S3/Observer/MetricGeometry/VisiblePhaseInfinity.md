# Visible-Phase Infinity of the Observer Distance

## Abstract

The ENNReal observable-supremum distance is infinite across distinct visible phases.

**Theorem 1.1 (Distinct visible phases have top observer distance).**

$$\forall tau x y, hphase \in H,\ projection(x)\neq projection(y) \Rightarrow observerDistance(tau,x,y) = \infty.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/VisiblePhaseInfinity.visible_phase_separation_distance_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distance is the supremum in ENNReal of the endpoint gaps of continuous complex observables whose read-update defect is at most one. If the update preserves the visible projection, the phase character obtained from AddCircle.toCircle has exactly zero defect. Scaling that character by every natural number gives admissible gaps with no finite upper bound. This is the finite observable-supremum shadow only; it does not claim a spectral triple, a bundle identification, or a type-II classification.

**Theorem 1.2 (A nonidentity hidden translation supplies the witness).**

$$\exists tau,\ tau\neq refl \land (\forall z, \operatorname{proj}(tau^{-1}z)=\operatorname{proj}(z)) \land\ \operatorname{proj}(\operatorname{flow}(0))\neq \operatorname{proj}(\operatorname{flow}(\frac{1}{2})) \land\ observerDistance(tau, \operatorname{flow}(0), \operatorname{flow}(\frac{1}{2})) = \infty.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/VisiblePhaseInfinity.hiddenTranslation_visible_phase_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The translation by the frozen nonzero hidden-unit offset is a genuine permutation of the solenoid. Its offset lies in the kernel of the visible projection, so the phase-preservation hypothesis holds. The real-flow points at zero and one half have distinct visible phases, and the main theorem therefore gives top distance for this concrete nonidentity update.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/VisiblePhaseInfinity.hiddenTranslation_visible_phase_witness`
- Truth anchor: `D5/S3/Observer/MetricGeometry/VisiblePhaseInfinity.visible_phase_separation_distance_eq_top`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](../../../S1/Dynamics/UniversalSolenoid.md)
- Dependency: [D5/S1/Solenoid/StreamlineDecomposition](../../../S1/Solenoid/StreamlineDecomposition.md)
- Dependency: [D5/S3/Observer/ObserverMetric](../ObserverMetric.md)
