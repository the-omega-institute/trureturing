# Transformation Description Bound

## Abstract

A compiler bounds target description cost by source and transformation costs.

**Theorem 1.1 (Compiled transformations have an additive description bound).**

$$K_{target}(y) \le K_{source}(x) + K_{transform}(u) + c.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound.transformation_description_complexity_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each description system records a realization relation and a natural-number code cost. An encoder supplies one description of every object, while the displayed complexity is the minimum cost among all realizing codes.

The compiler combines a code for u with a code for x. Its correctness field makes the combined code realize y whenever u carries x to y, and its cost field charges at most the two input costs plus the fixed overhead c.

The proof extracts minimum-cost source and transformation codes, compiles them, and uses target minimality. The natural-number addition model in the Lean module witnesses that the premises are inhabited at positive cost.

Pinned Mathlib and public Lean repositories were searched before proving. No matching description-complexity model or transformation bound was found. The proof reuses Nat.find_min' for the least-witness inequality and keeps the realization and compiler semantics explicit.

This is an honest partial closure of the leading forward bound in source proposition 3.5. Its reverse bound, absolute-difference consequence, and logarithmic-tightness construction remain residual and are not asserted.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound.transformation_description_complexity_le`
