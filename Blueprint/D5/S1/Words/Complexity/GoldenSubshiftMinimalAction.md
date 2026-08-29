# The Minimal Forward-Shift Action on the Golden Subshift

## Abstract

Forward shifts act on every word subshift, their subtype orbits have the expected ambient ranges, and the frozen golden orbit-closure result registers the golden subshift as a minimal natural-number action.

For a one-sided word x, write X_x for its prefix-language subshift. The ambient density theorem for X_g is already frozen. This node exposes the iterated shift lemma needed by downstream imports, installs the natural-number action on the subshift subtype, identifies its orbit after coercion to the ambient sequence space, and transfers the frozen result through Subtype.dense_iff to register the minimal-action instance.

**Theorem 1.1 (Every iterated forward shift remains in the word subshift).**

$$y \in X_x \Rightarrow \forall i \in \mathbb{N}, \sigma^{i}(y) \in X_x$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.shift_mem_wordSubshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GoldenSubshiftMinimality keeps this general form private, and SubshiftTopology privately keeps only the special case where the member is the generating word itself. The zero case is the given membership, and the successor case uses the existing one-step shift invariance. Its role is reuse, not an additional mathematical strengthening.

**Theorem 1.2 (Forward shifts define a natural-number action on each word subshift).**

$$\forall x, \operatorname{AddAction}(\mathbb{N}, X_x)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.shiftAddAction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action sends (i,y) to the subtype point represented by shift i y; the preceding theorem supplies its membership proof. FullShift.shift_zero and FullShift.shift_add supply the two action laws, the latter after commuting the two indices because mathlib states iterated shifts in the opposite composition order. Mathlib provides those laws for the ambient shift but does not install this action instance on the subshift subtype.

**Theorem 1.3 (The coerced subtype orbit is the ambient forward-shift range).**

$$\operatorname{val}(\operatorname{Orb}(\mathbb{N}, y)) = \operatorname{range}(i \mapsto \sigma^{i}(y))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.coe_orbit_eq_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding the registered scalar action shows pointwise that coercing an orbit element gives the corresponding ambient forward shift. The two set inclusions then identify the image of the subtype orbit with the range indexed by natural shift times.

**Theorem 1.4 (The golden subshift carries the minimal forward-shift action).**

$$\operatorname{IsMinimal}(\mathbb{N}, X_g)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.goldenSubshiftIsMinimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a point of the golden subshift subtype, coe_orbit_eq_range rewrites the coerced action orbit as its ambient forward-shift range. The frozen golden_wordSubshift_minimal theorem supplies the ambient closure equality. Subtype.dense_iff transfers that equality to density in the subtype, and this node records the result as the mathlib AddAction.IsMinimal instance.

## References

- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.coe_orbit_eq_range`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.goldenSubshiftIsMinimal`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.shiftAddAction`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftMinimalAction.shift_mem_wordSubshift`
- Dependency: [D5/S1/Words/Complexity/GoldenSubshiftMinimality](GoldenSubshiftMinimality.md)
