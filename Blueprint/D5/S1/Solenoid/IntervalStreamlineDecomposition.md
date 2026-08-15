# Unit-Interval Streamline Decomposition

## Abstract

Every continuous unit-interval solenoid path has a continuous real lift and a constant hidden offset.

**Theorem 1.1 (Every unit-interval path has a constant hidden offset).**

$$\forall \gamma\in C([0, 1], \mathcal{S}),\ \exists x\in C([0, 1], \mathbb{R}),\ \exists c\in \ker(\pi),\ \forall t,\ \gamma(t)= realFlow(x(t))+ c.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/IntervalStreamlineDecomposition.exists_interval_streamline_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extend the interval path continuously to the real line using the canonical clamping map. The frozen normalized streamline theorem then supplies a continuous real lift and one element of the projection kernel that reconstruct the extended path. Restricting the lift to the unit interval gives the stated decomposition.

The projection kernel is precisely the compatible hidden family: one kernel element is used for every time, so the hidden coordinate is constant while the real lift remains continuous.

Pinned Mathlib supplies ContinuousMap.IccExtendCM and its restriction identity. The universal-solenoid decomposition itself is imported from the frozen streamline module and applied directly.

## References

- Truth anchor: `D5/S1/Solenoid/IntervalStreamlineDecomposition.exists_interval_streamline_decomposition`
- Dependency: [D5/S1/Solenoid/StreamlineDecomposition](StreamlineDecomposition.md)
