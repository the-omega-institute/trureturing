# Finite Prefix Reflection for Infinite Word Sets

## Abstract

Closed one-sided word sets are recovered from finite prefix cylinders, and shift invariance descends to finite stages.

For a set S of one-sided words over a discrete alphabet, prefixCylinder S n collects the length-n cylinders through S. These finite observations reconstruct every closed S and provide the transition law for a forward shift.

**Theorem 1.1 (Finite prefix cylinders are open).**

$$\operatorname{IsOpen} prefixCylinder S n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PrefixLanguageTopology.isOpen_prefixCylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set is a union of product cylinders, so the discrete product basis makes openness immediate.

**Theorem 1.2 (Finite prefix cylinders are closed).**

$$\operatorname{IsClosed} prefixCylinder S n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PrefixLanguageTopology.isClosed_prefixCylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complement is the union of cylinders with the same finite prefix length, so it is open in the discrete product basis.

**Theorem 1.3 (Closed sets are reconstructed by all finite prefixes).**

$$S = intersectionn prefixCylinder S n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PrefixLanguageTopology.closed_eq_iInter_prefixCylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point outside a closed set is excluded by one finite cylinder from the product basis; a point in the set supplies a witness at every level.

**Theorem 1.4 (All finite prefixes reconstruct the closure).**

$$closure S = intersectionn prefixCylinder S n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PrefixLanguageTopology.closure_eq_iInter_prefixCylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each prefix approximation is clopen, so their intersection is closed; the product basis separates every point outside the closure.

**Theorem 1.5 (Shift invariance descends one prefix stage).**

$$x \in prefixCylinder S n+1 \Rightarrow shift x \in prefixCylinder S n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PrefixLanguageTopology.shift_mem_prefixCylinder_of_mem_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement through n+1 coordinates transports to agreement through n coordinates after dropping the first coordinate.

## References

- Truth anchor: `D5/S1/Words/Complexity/PrefixLanguageTopology.closed_eq_iInter_prefixCylinder`
- Truth anchor: `D5/S1/Words/Complexity/PrefixLanguageTopology.closure_eq_iInter_prefixCylinder`
- Truth anchor: `D5/S1/Words/Complexity/PrefixLanguageTopology.isClosed_prefixCylinder`
- Truth anchor: `D5/S1/Words/Complexity/PrefixLanguageTopology.isOpen_prefixCylinder`
- Truth anchor: `D5/S1/Words/Complexity/PrefixLanguageTopology.shift_mem_prefixCylinder_of_mem_succ`
